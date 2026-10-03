import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.Submersion
import Mathlib.Geometry.Manifold.ContMDiffMap

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_unique_nearest_submersion_iUnion_of_local
    {ι : Type*} (U : ι → TopologicalSpace.Opens H)
    (W : Set H) [ChartedSpace E W] [IsManifold 𝓘(ℝ, E) ∞ W]
    (P : ∀ i, C^∞⟮𝓘(ℝ, H), U i; 𝓘(ℝ, E), W⟯)
    (hsub : ∀ i, _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ (P i))
    (hnearest : ∀ i (z : U i),
      IsMinOn (fun y => dist (z : H) y) W (P i z : H) ∧
      (∀ y ∈ W, IsMinOn (fun w => dist (z : H) w) W y → y = (P i z : H))) :
    let Ω : TopologicalSpace.Opens H :=
      ⟨⋃ i, (U i : Set H), isOpen_iUnion (fun i => (U i).isOpen)⟩
    ∃ Q : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, E), W⟯,
      _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Q ∧
      (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) W (Q z : H) ∧
        (∀ y ∈ W, IsMinOn (fun w => dist (z : H) w) W y → y = (Q z : H))) ∧
      ∀ i (z : U i), Q ⟨(z : H), mem_iUnion.mpr ⟨i, z.property⟩⟩ = P i z := by
  classical
  let Ω : TopologicalSpace.Opens H :=
    ⟨⋃ i, (U i : Set H), isOpen_iUnion (fun i => (U i).isOpen)⟩
  have hcover (z : Ω) : ∃ i, (z : H) ∈ U i := mem_iUnion.mp z.property
  let index : Ω → ι := fun z => (hcover z).choose
  have hindex (z : Ω) : (z : H) ∈ U (index z) := (hcover z).choose_spec
  let Q : Ω → W := fun z => P (index z) ⟨(z : H), hindex z⟩
  have hQnearest (z : Ω) :
      IsMinOn (fun y => dist (z : H) y) W (Q z : H) ∧
      (∀ y ∈ W, IsMinOn (fun w => dist (z : H) w) W y → y = (Q z : H)) :=
    hnearest (index z) ⟨(z : H), hindex z⟩
  have hincl (i : ι) : U i ≤ Ω := fun _ hz => mem_iUnion.mpr ⟨i, hz⟩
  have hagree (i : ι) (z : U i) :
      Q (TopologicalSpace.Opens.inclusion (hincl i) z) = P i z := by
    apply Subtype.ext
    exact (hnearest i z).2 _ (Q (TopologicalSpace.Opens.inclusion (hincl i) z)).property
      (hQnearest (TopologicalSpace.Opens.inclusion (hincl i) z)).1
  have hQsmooth : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Q := by
    intro z
    obtain ⟨i, hzi⟩ := hcover z
    let V : TopologicalSpace.Opens Ω :=
      ⟨Subtype.val ⁻¹' (U i : Set H), (U i).isOpen.preimage continuous_subtype_val⟩
    let j : V → U i := fun y => ⟨((y : Ω) : H), y.property⟩
    have hj : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ j := by
      apply (ContMDiff.subtypeVal_comp_iff (U i) j).mp
      exact (contMDiff_subtype_val (I := 𝓘(ℝ, H)) (U := Ω)).comp
        (contMDiff_subtype_val (I := 𝓘(ℝ, H)) (U := V))
    have hv : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ (fun y : V => Q (y : Ω)) := by
      apply ((P i).contMDiff.comp hj).congr
      intro y
      exact hagree i (j y)
    exact contMDiffAt_subtype_iff.mp (hv.contMDiffAt (x := (⟨z, hzi⟩ : V)))
  have hQsub : _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Q := by
    apply isSubmersion_of_surjective_mfderiv Q hQsmooth
    intro z
    obtain ⟨i, hzi⟩ := hcover z
    let x : U i := ⟨(z : H), hzi⟩
    have heq : (Q ∘ TopologicalSpace.Opens.inclusion (hincl i)) = P i :=
      funext (hagree i)
    have hder : mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) (P i) x =
        mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Q
          (TopologicalSpace.Opens.inclusion (hincl i) x) := by
      have hc := mfderiv_comp x
        (hQsmooth.mdifferentiableAt (by simp))
        ((contMDiff_inclusion (n := ∞) (hincl i)).mdifferentiableAt (by simp))
      rw [heq, DifferentialGeometry.mfderiv_opens_incl] at hc
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun A => A v) hc
    change Function.Surjective (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Q
      (TopologicalSpace.Opens.inclusion (hincl i) x))
    rw [← hder]
    exact (mfderiv_hasRightInverse_of_isSubmersionAt ((hsub i).isSubmersionAt x)).surjective
  exact ⟨⟨Q, hQsmooth⟩, hQsub, hQnearest, hagree⟩

end DifferentialGeometry.Topology.Manifold
