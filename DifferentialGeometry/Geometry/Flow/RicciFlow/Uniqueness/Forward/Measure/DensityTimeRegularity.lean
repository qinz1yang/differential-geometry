import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Tensor.Coordinates
open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless]

theorem forward_uniqueness_density_dot_continuous
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    Continuous (fun x => forwardUniqueDensityDot (I := I) g₁ g₂
      (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂))
      (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)) t x) := by
  have hab : a < b := ht.1.trans ht.2
  have hg₁ (α : M) (i j : Fin (Module.finrank ℝ E)) :=
    (hjoint₁ α i j).mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hg₂ (α : M) (i j : Fin (Module.finrank ℝ E)) :=
    (hjoint₂ α i j).mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  have hS₁ := forwardUniquenessIsSolution (I := I) g₁ hab hjoint₁ hpde₁
  have hS₂ := forwardUniquenessIsSolution (I := I) g₂ hab hjoint₂ hpde₂
  have hdens (x : M) := density_hasDerivAt (I := I) g₁ g₂
    (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂))
    (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂))
    (fun X Y => pde_hasDerivAt (I := I) g₁ hpde₁ ht x X Y)
    (fun X Y => pde_hasDerivAt (I := I) g₂ hpde₂ ht x X Y)
    (connSpeed_hasDerivAt (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (forwardUniquenessGamma (I := I) g₁ g₂ hab hjoint₁ hjoint₂ hpde₁ hpde₂ t ht x))
    (rmSpeed_hasDerivAt (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)
      (pde_hasDerivAt (I := I) g₁ hpde₁ ht x)
      (forwardUniquenessRm (I := I) g₁ g₂ hS₁ hS₂ hpde₁ hpde₂ t ht x))
  have hdenSmooth := dens_jointContMDiffOn (I := I) g₁ g₂ hg₁ hg₂
  have hdCont : ContinuousOn
      (fun p : ℝ × M => deriv (fun s => forwardUniqueDensity (I := I) g₁ g₂ s p.2) p.1)
      (Ioo a b ×ˢ (univ : Set M)) := by
    intro p hp
    have hat : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => forwardUniqueDensity (I := I) g₁ g₂ q.1 q.2) p :=
      hdenSmooth.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
    have hdAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => deriv (fun s => forwardUniqueDensity (I := I) g₁ g₂ s q.2) q.1) p :=
      DifferentialGeometry.timeDeriv_smoothAt hat (by simp)
    exact hdAt.continuousAt.continuousWithinAt
  have hc : Continuous (fun x => deriv (fun s => forwardUniqueDensity (I := I) g₁ g₂ s x) t) := by
    have hslice : Continuous (fun x : M => (t, x)) := continuous_const.prodMk continuous_id
    have hmap : MapsTo (fun x : M => (t, x)) univ (Ioo a b ×ˢ (univ : Set M)) :=
      fun _ _ => ⟨ht, mem_univ _⟩
    have hcomp := hdCont.comp_continuous hslice (fun x => hmap (mem_univ x))
    simpa only [Function.comp_def] using hcomp
  exact hc.congr fun x => (hdens x).deriv

end DifferentialGeometry.PDE.RicciFlow
