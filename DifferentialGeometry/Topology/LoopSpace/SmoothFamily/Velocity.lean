import DifferentialGeometry.Topology.LoopSpace.SmoothFamily.Defs
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def LoopFamilyVelocityExtension (a b : ℝ) (γ : ℝ → DifferentialGeometry.Topology.freeLoop M) : Prop :=
  ∃ X : ℝ → (p : M) → TangentSpace I p,
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) ∧
    (∀ t ∈ Ico a b, ∀ z : DifferentialGeometry.Topology.loopCircle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Ici t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))) ∧
    ∀ t ∈ Ioc a b, ∀ z : DifferentialGeometry.Topology.loopCircle,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => γ s z) (Iic t) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t z)))

theorem loopFamilyVelocityExtension_zero (a b : ℝ)
    (γ : ℝ → DifferentialGeometry.Topology.freeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t') :
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

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {a b : ℝ}

theorem loopFamilyVelocityExtension_of_subset {a' b' : ℝ} {γ : ℝ → DifferentialGeometry.Topology.freeLoop M}
    (ha : a' ≤ a) (hb : b ≤ b') (h : LoopFamilyVelocityExtension (I := I) a' b' γ) :
    LoopFamilyVelocityExtension (I := I) a b γ := by
  obtain ⟨X, hX, hIco, hIoc⟩ := h
  exact ⟨X, hX,
    fun t ht z => hIco t ⟨le_trans ha ht.1, lt_of_lt_of_le ht.2 hb⟩ z,
    fun t ht z => hIoc t ⟨lt_of_le_of_lt ha ht.1, le_trans ht.2 hb⟩ z⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening


section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [SigmaCompactSpace M]
variable {a b : ℝ}

def LoopFamilyVelocityExtensionProducer (a b : ℝ) : Prop :=
  ∀ γ : ℝ → DifferentialGeometry.Topology.freeLoop M,
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
    (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
    (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
    LoopFamilyVelocityExtension (I := I) a b γ

omit [CompleteSpace E] [FiniteDimensional ℝ E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionProducer_of_allWindows
    (h : ∀ (a' b' : ℝ) (γ : ℝ → DifferentialGeometry.Topology.freeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a' b') →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a' b') →
      (∀ t ∈ Icc a' b', Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtension (I := I) a' b' γ) :
    LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  fun γ hγ hi hemb => h a b γ hγ hi hemb

end Manifold

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def HasBoundaryIsotopyVelocityExtension (a b : ℝ) : Prop :=
  ∀ γ : ℝ → DifferentialGeometry.Topology.freeLoop M,
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
    (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
    (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
    LoopFamilyVelocityExtension (I := I) a b γ

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end
