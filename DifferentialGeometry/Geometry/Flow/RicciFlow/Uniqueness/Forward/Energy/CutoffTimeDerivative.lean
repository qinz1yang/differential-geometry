import DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.SmoothSolutions

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

theorem forward_uniqueness_cutoff_energy_hasDerivAt
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ))
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
    HasDerivAt
      (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily g₁ s)
      (∫ x, χ x ^ 2 *
        (forwardUniqueDensityDot (I := I) g₁ g₂
          (connSpeed (I := I) g₁ g₂ (forwardUniquenessAvec (I := I) g₁ g₂))
          (rmSpeed (I := I) g₁ g₂ (forwardUniquenessSvec (I := I) g₁ g₂)) t x +
          (1 / 2) * traceTimeDerivMetric (I := I) g₁ t x *
            forwardUniqueDensity (I := I) g₁ g₂ t x)
        ∂riemannianMeasureFamily g₁ t) t := by
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
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => χ p.2 ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (Ioo a b ×ˢ (univ : Set M)) :=
    ((χ.contMDiff.comp contMDiff_snd).pow 2).contMDiffOn.mul
      (dens_jointContMDiffOn (I := I) g₁ g₂ hg₁ hg₂)
  have hd := hasDerivAt_integral_riemannianMeasureFamily_of_compact_support
    g₁ isOpen_Ioo hg₁ (fun s x => χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x)
    (hf.of_le (by simp)) hχ (fun s _ x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) ht
  convert hd using 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [((hdens x).const_mul (χ x ^ 2)).deriv]
  ring

end DifferentialGeometry.PDE.RicciFlow
