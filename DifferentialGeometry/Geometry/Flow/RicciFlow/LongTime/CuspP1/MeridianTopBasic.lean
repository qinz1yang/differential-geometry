import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicPrimitiveBasic
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SimplyConnectedTarget
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.ContinuousFilling

/-!
# CP1-Q3 (basic): degree-class kernel => continuous filling disk

* `nullhomotopic_of_loopDegreeClass_eq_one_CPQ`: `loopDegreeClass γ 1 = 1` implies `γ` nullhomotopic.
* `exists_disk_of_ker_CPQ`: `loopDegreeClass loop 1 ∈ ker (π₁.map φ)` for `φ : C(Torus, R)`
  gives a continuous disk in the ambient space bounding `(val ∘ φ) ∘ loop`, with range in `R`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set Function
open scoped ContinuousMap
namespace GC.LongTime.CuspP1

section
variable {Q : Type*} [TopologicalSpace Q]

theorem nullhomotopic_of_loopDegreeClass_eq_one_CPQ (γ : freeLoop Q)
    (h : loopDegreeClass γ 1 = 1) : γ.Nullhomotopic := by
  let q := γ 0
  let p := circleToPath (⟨γ, rfl⟩ : basedCircleLoop q)
  have hp : Path.Homotopic p (Path.refl q) := by
    have h1 : loopDegreeClass γ 1 = Path.Homotopic.Quotient.mk p := by
      unfold loopDegreeClass
      rw [intLoop_one]
    have h2 : (1 : FundamentalGroup Q q) = Path.Homotopic.Quotient.mk (Path.refl q) := rfl
    rw [h1, h2] at h
    exact Quotient.exact h
  obtain ⟨H⟩ := hp
  have hH : Continuous H.eval := Path.continuous_uncurry_iff.mp H.continuous
  have hc : Continuous (fun t => pathToCircle (H.eval t)) := continuous_pathToCircle.comp hH
  refine ⟨q, ⟨⟨⟨fun z => pathToCircle (H.eval z.1) z.2,
    (FreeLoop.continuous_family_iff _).mp hc⟩, ?_, ?_⟩⟩⟩
  · intro θ
    change pathToCircle (H.eval 0) θ = γ θ
    rw [H.eval_zero]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe p t
  · intro θ
    change pathToCircle (H.eval 1) θ = q
    rw [H.eval_one]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe (Path.refl q) t

end

theorem exists_disk_of_ker_CPQ {X A : Type*} [TopologicalSpace X] [TopologicalSpace A] {R : Set A}
    (φ : C(X, ↥R)) (loop : freeLoop X)
    (hk : loopDegreeClass loop 1 ∈ (FundamentalGroup.map φ (loop 0)).ker) :
    ∃ u : C(closedDisk, A), diskTrace u = (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ φ).comp loop ∧
      Set.range u ⊆ R := by
  have hk' : FundamentalGroup.map φ (loop 0) (loopDegreeClass loop 1) = 1 := hk
  have hn : (φ.comp loop).Nullhomotopic := by
    apply nullhomotopic_of_loopDegreeClass_eq_one_CPQ
    have h : loopDegreeClass (φ.comp loop) 1 =
        FundamentalGroup.map φ (loop 0) (loopDegreeClass loop 1) := by
      unfold loopDegreeClass
      change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
      congr 1
    rw [h]
    exact hk'
  obtain ⟨u, hu⟩ := (nullhomotopic_iff_exists_continuous_disk _).mp hn
  refine ⟨(ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ u), ?_, ?_⟩
  · change ((ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ u).comp diskBoundary) = _
    rw [ContinuousMap.comp_assoc]
    change ContinuousMap.comp _ (diskTrace u) = _
    rw [hu]
    rfl
  · rintro _ ⟨z, rfl⟩
    exact (u z).2

end GC.LongTime.CuspP1
