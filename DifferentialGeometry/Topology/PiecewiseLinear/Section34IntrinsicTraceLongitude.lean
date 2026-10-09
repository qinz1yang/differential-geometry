/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicMeridianSystem
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridianLongitude

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem exists_primitive_intrinsic_marked_meridian_coordinates
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hJ : IsPLSphere 1 J) (hJΘ : J ⊆ frontier P)
    (hcarry : CarriesFirstHomologyOnto (u '' J)
      (section34FaceTorus (section34VertexBallImage src f₁) s)) :
    ∃ (M Q : Set E3) (f : E3 × E3 → E3)
      (hf : IsPLHomeomorphOn f (M ×ˢ Q) (frontier P))
      (p : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1} → Q)
      (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
      (eQ : integralSingularHomology 1 Q ≃ₗ[ℤ] ℤ),
      IsPLSphere 1 M ∧ IsPLSphere 1 Q ∧ Function.Injective p ∧
        (∀ e, Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e.1 =
          f '' (M ×ˢ {(p e : E3)})) ∧
        let φ := (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
        let ρ := ContinuousMap.snd.comp ((φ.symm : C(_, M × Q)).comp
          (⟨inclusion hJΘ, continuous_inclusion hJΘ⟩ : C(J, _)))
        (∀ x : J, Function.Surjective (FundamentalGroup.map ρ x)) ∧
          (eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = 1 ∨
            eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = -1) := by
  obtain ⟨M, Q, f, p, hM, hQ, hf, hp, hpinj, hmarked, hdisks⟩ :=
    split_disks_form_intrinsic_marked_meridian_system hcut hf₁ s hP hu hUP
  let φ : (M × Q) ≃ₜ frontier P :=
    (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
  let p' : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1} → Q :=
    fun e => ⟨p e, hp e⟩
  have hp'inj : Function.Injective p' := by
    intro a b hab
    exact hpinj (congrArg Subtype.val hab)
  obtain ⟨-, hsubdiv, hmap, -⟩ := id hcut
  obtain ⟨n, v, -, hv, -⟩ :=
    exists_cycle_order_intrinsic_face_vertex_balls hcut hf₁ s hu hUP
  obtain ⟨e, _, _, he, _, _⟩ :=
    exists_section34EdgeIndex_pair_of_incident hsubdiv hmap s (v 0) ((hv _).mpr ⟨0, rfl⟩)
  let i : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1} := ⟨e, he⟩
  let D := Function.invFunOn u P '' section34SplitDiskImage src f₁ e
  obtain ⟨r, hr, -⟩ := (hcut.intrinsic_splitDisk_meridian hf₁ s hu hUP e he).1
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hDP : D ⊆ P := (hdisks i).1
  have hfiber : ∀ m : M, (φ (m, p' i) : E3) ∈ D := by
    intro m
    apply image_mono (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
    rw [hmarked i]
    exact ⟨((m : E3), p i), ⟨m.property, rfl⟩, rfl⟩
  have hJP : J ⊆ P := hJΘ.trans hP.isPolyhedron.isClosed.frontier_subset
  have hmodelcarry : CarriesFirstHomologyOnto J P :=
    hP.carriesFirstHomologyOnto_of_image hu hJ.isPolyhedron hJ.isPathConnected_one hJP
      (by rw [hUP]; exact hcarry)
  obtain ⟨eJ, eQ, hdegree⟩ := exists_primitive_longitude_coordinates_of_meridian_disk
    hP.1 hJ hQ φ hJΘ hmodelcarry hD hDP (p' i) hfiber
  refine ⟨M, Q, f, hf, p', eJ, eQ, hM, hQ, hp'inj, hmarked, ?_⟩
  exact ⟨fun x => surjective_longitude_fundamentalGroup_of_meridian_disk
    hP.1 hJ hQ φ hJΘ hmodelcarry hD hDP (p' i) hfiber x, hdegree⟩

end DifferentialGeometry.Topology.PiecewiseLinear
