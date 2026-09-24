import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopModel

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def curveOfLoopFamily (γ : ℝ → ContinuousFreeLoop M) : CurveMap M := fun z t => γ t z

def LoopFamilyVelocityExtension (a b : ℝ) (γ : ℝ → ContinuousFreeLoop M) : Prop :=
  ∃ X : ℝ → (p : M) → TangentSpace I p,
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) ∧
    (∀ t ∈ Ico a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Ici t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))) ∧
    ∀ t ∈ Ioc a b, ∀ z : Surgery.Topology.Circle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Iic t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))

theorem loopFamilyVelocityExtension_zero (a b : ℝ)
    (γ : ℝ → ContinuousFreeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t') :
    LoopFamilyVelocityExtension (I := I) a b γ := by
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I) (n := ∞))
  · intro t _ z
    have hpt : (fun s : ℝ => γ s z) = fun _ : ℝ => γ t z := by
      funext s
      rw [hconst s t]
    rw [hpt, ContinuousLinearMap.smulRight_zero]
    exact hasMFDerivWithinAt_const (γ t z) (Ici t) t
  · intro t _ z
    have hpt : (fun s : ℝ => γ s z) = fun _ : ℝ => γ t z := by
      funext s
      rw [hconst s t]
    rw [hpt, ContinuousLinearMap.smulRight_zero]
    exact hasMFDerivWithinAt_const (γ t z) (Iic t) t

def LiftLoopFamily (X : ℝ → (p : M) → TangentSpace I p) :
    ℝ → (p : ℝ × M) → TangentSpace (𝓘(ℝ,ℝ).prod I) p :=
  fun _ (q : ℝ × M) => ((1:ℝ), X q.1 q.2)

theorem liftLoopFamily_contMDiff (X : ℝ → (p : M) → TangentSpace I p)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) ∞
      (fun p : ℝ × M => (⟨p, LiftLoopFamily (I := I) X p.1 p⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
  DifferentialGeometry.Analysis.ODE.autonomizedFlowVF_section_contMDiff (I := I) X hX

variable {a b : ℝ}

theorem loopFamilyVelocityExtension_of_subset {a' b' : ℝ} {γ : ℝ → ContinuousFreeLoop M}
    (ha : a' ≤ a) (hb : b ≤ b') (h : LoopFamilyVelocityExtension (I := I) a' b' γ) :
    LoopFamilyVelocityExtension (I := I) a b γ := by
  obtain ⟨X, hX, hIco, hIoc⟩ := h
  exact ⟨X, hX,
    fun t ht z => hIco t ⟨le_trans ha ht.1, lt_of_lt_of_le ht.2 hb⟩ z,
    fun t ht z => hIoc t ⟨lt_of_le_of_lt ha ht.1, le_trans ht.2 hb⟩ z⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
