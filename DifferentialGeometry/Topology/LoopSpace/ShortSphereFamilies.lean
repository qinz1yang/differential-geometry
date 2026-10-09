import DifferentialGeometry.Topology.LoopSpace.ShortFamilies
import DifferentialGeometry.Topology.LoopSpace.RegularFamily
import DifferentialGeometry.Topology.Homotopy.SphereVanishing








noncomputable section

open Set Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M] [Nonempty M]




theorem exists_short_sphere_family_null_radius (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e p))
    (hpi : ∀ q : M, Subsingleton (HomotopyGroup (Fin 2) M q)) :
    ∃ σ : ℝ≥0, 0 < σ ∧
      ∀ Γ : regularSphereFamily e (he.of_le (by exact_mod_cast le_top)),
        (∀ k, riemannianCurveLength g (fun t => (Γ k).val.val (t : loopCircle)) 0 1 < σ) →
        ∃ q : M, LoopFamily.classOf
          (regularSphereFamilyInclusion e (he.of_le (by exact_mod_cast le_top)) hemb Γ) =
            LoopFamily.nullClass q := by
  let he₁ := he.of_le (show (1 : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast le_top)
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he₁
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he₁
  obtain ⟨σ, _, hσ, _, _, hfamily⟩ := exists_short_loop_and_family_filling g e he hemb hi
  refine ⟨σ, hσ, fun Γ hshort => ?_⟩
  have hΓ : Continuous (fun k => (Γ k).val) :=
    (continuous_regularContractibleLoop_iff e he₁ Γ).mp Γ.continuous
  obtain ⟨R, hR, hR0, hR1, hnull, _⟩ :=
    hfamily familySphere (fun k => (Γ k).val) hΓ hshort
  let C : C(familySphere, M) := ContractibleLoop.evaluation.comp
    (regularSphereFamilyInclusion e he₁ hemb Γ)
  let H : (regularSphereFamilyInclusion e he₁ hemb Γ).Homotopy (LoopFamily.constants C) := {
    toFun := fun z => ⟨(R z).val, hnull z⟩
    continuous_toFun := ((continuous_regularLoop_inclusion e he₁ hemb).comp hR).subtype_mk _
    map_zero_left := fun k => by
      apply Subtype.ext
      exact congrArg (fun γ : regularLoop E M => γ.val) (hR0 k)
    map_one_left := fun k => by
      apply Subtype.ext
      exact congrArg (fun γ : regularLoop E M => γ.val) (hR1 k) }
  obtain ⟨q, hq⟩ := familySphereMap_nullhomotopic_of_piTwo hpi C
  refine ⟨q, (LoopFamily.classOf_eq_iff _ _).mpr ?_⟩
  have hH : (regularSphereFamilyInclusion e he₁ hemb Γ).Homotopic (LoopFamily.constants C) := ⟨H⟩
  exact hH.trans ((ContinuousMap.Homotopic.refl ContractibleLoop.constants).comp hq)

end DifferentialGeometry.Topology
