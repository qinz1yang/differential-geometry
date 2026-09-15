import DifferentialGeometry.Bundle.VelocityLift

section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {P : Type*} [TopologicalSpace P]

theorem continuousOn_velocityLift_slice_of_leftInverse
    (f : 𝕜 → P → M) (e : M → F) (r : F → M) {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(𝕜, F) I 1 r U) {J : Set P}
    (hmem : ∀ x t, t ∈ J → e (f x t) ∈ U)
    (hleft : ∀ x t, t ∈ J → r (e (f x t)) = f x t)
    (hslice : ∀ t ∈ J, Differentiable 𝕜 (fun x => e (f x t)))
    (hval : ContinuousOn (fun p : 𝕜 × P => e (f p.1 p.2)) (univ ×ˢ J))
    (hder : ContinuousOn (fun p : 𝕜 × P => deriv (fun x => e (f x p.2)) p.1)
      (univ ×ˢ J)) :
    ContinuousOn (fun p : 𝕜 × P => velocityLift (I := I) (fun x => f x p.2) p.1)
      (univ ×ˢ J) := by
  let L : 𝕜 × P → TangentBundle 𝓘(𝕜, F) F := fun p =>
    ⟨e (f p.1 p.2), deriv (fun x => e (f x p.2)) p.1⟩
  have hL : ContinuousOn L (univ ×ˢ J) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(𝕜, F)).symm.continuous.comp_continuousOn
      (hval.prodMk hder)
  have hcomp := (hr.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn).comp hL
    (fun p hp => hmem p.1 p.2 hp.2)
  apply hcomp.congr
  intro p hp
  have hrp : MDifferentiableAt 𝓘(𝕜, F) I r (e (f p.1 p.2)) :=
    ((hr _ (hmem p.1 p.2 hp.2)).contMDiffAt (hU.mem_nhds (hmem p.1 p.2 hp.2))).mdifferentiableAt (by norm_num)
  have hs : MDifferentiableAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, F) (fun x => e (f x p.2)) p.1 :=
    (hslice p.2 hp.2 p.1).mdifferentiableAt
  have heq : (fun x => r (e (f x p.2))) = (fun x => f x p.2) :=
    funext (fun x => hleft x p.2 hp.2)
  have ht := tangentMap_comp_at (I := 𝓘(𝕜, 𝕜)) (I' := 𝓘(𝕜, F)) (I'' := I)
    (f := fun x => e (f x p.2)) (g := r) ⟨p.1, (1 : 𝕜)⟩ hrp hs
  have hte : tangentMap 𝓘(𝕜, 𝕜) 𝓘(𝕜, F)
      (fun x => e (f x p.2)) ⟨p.1, (1 : 𝕜)⟩ = L p := by
    change (⟨e (f p.1 p.2),
      mfderiv 𝓘(𝕜, 𝕜) 𝓘(𝕜, F) (fun x => e (f x p.2)) p.1 (1 : 𝕜)⟩ :
      TangentBundle 𝓘(𝕜, F) F) = L p
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun v : F => (⟨e (f p.1 p.2), v⟩ : TangentBundle 𝓘(𝕜, F) F))
      (fderiv_apply_one_eq_deriv (f := fun x => e (f x p.2)) (x := p.1))
  have htr : tangentMapWithin 𝓘(𝕜, F) I r U (L p) =
      tangentMap 𝓘(𝕜, F) I r (L p) :=
    tangentMapWithin_eq_tangentMap (hU.uniqueMDiffOn _ (hmem p.1 p.2 hp.2)) hrp
  have ht' : tangentMap 𝓘(𝕜, 𝕜) I (fun x => r (e (f x p.2)))
      ⟨p.1, (1 : 𝕜)⟩ = tangentMap 𝓘(𝕜, F) I r (L p) := by
    rw [← hte]
    exact ht
  rw [heq] at ht'
  exact ht'.trans htr.symm


end DifferentialGeometry

end
