import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators
import Mathlib.Topology.Order.ProjIcc
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusOnPolyhedralCylinder

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.carriesFundamentalGroupOnto_first_of_second {M : Type*}
    [TopologicalSpace M] [T2Space M] {A A₀ A₁ T : Set M}
    (hA : IsAnnulusOn A A₀ A₁) (hAT : A ⊆ T)
    (hcarry : CarriesFundamentalGroupOnto A₁ T) : CarriesFundamentalGroupOnto A₀ T := by
  obtain ⟨φ, h₀, h₁⟩ := hA
  let f (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ) : M :=
    φ (p.1, projIcc 0 1 zero_le_one p.2)
  have hf : Continuous f := continuous_subtype_val.comp
    (φ.continuous.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)))
  have hlevel (t : Set.Icc (0 : ℝ) 1) :
      (fun x => f (x, (t : ℝ))) '' univ =
        Subtype.val '' (φ '' {p | (p.2 : ℝ) = (t : ℝ)}) := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      refine ⟨φ (x, t), ⟨(x, t), rfl, rfl⟩, ?_⟩
      simp only [f, projIcc_of_mem zero_le_one t.2]
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      have heq : p.2 = t := Subtype.ext hp
      refine ⟨p.1, mem_univ _, ?_⟩
      simp only [f, projIcc_of_mem zero_le_one t.2]
      exact congrArg (fun q => (φ q : M)) (Prod.ext rfl heq.symm)
  have hzero : (fun x => f (x, (0 : ℝ))) '' univ = A₀ := (hlevel 0).trans h₀.symm
  have hone : (fun x => f (x, (1 : ℝ))) '' univ = A₁ := (hlevel 1).trans h₁.symm
  rw [← hzero]
  apply carriesFundamentalGroupOnto_image_zero_of_image_one isCompact_univ hf.continuousOn
    (fun p _ => hAT (φ (p.1, projIcc 0 1 zero_le_one p.2)).2)
  · intro x _ y _ hxy
    exact congrArg Prod.fst (φ.injective (Subtype.ext hxy))
  · rwa [hone]

theorem IsAnnulusOn.carriesFundamentalGroupOnto_ends_iff {M : Type*}
    [TopologicalSpace M] [T2Space M] {A A₀ A₁ T : Set M}
    (hA : IsAnnulusOn A A₀ A₁) (hAT : A ⊆ T) :
    CarriesFundamentalGroupOnto A₀ T ↔ CarriesFundamentalGroupOnto A₁ T :=
  ⟨hA.symm.carriesFundamentalGroupOnto_first_of_second hAT,
    hA.carriesFundamentalGroupOnto_first_of_second hAT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
