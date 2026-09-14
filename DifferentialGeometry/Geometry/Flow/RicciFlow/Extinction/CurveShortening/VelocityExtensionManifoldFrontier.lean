import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionEuclidean

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [SigmaCompactSpace M]
variable {a b : ℝ}

/-- The single analytic input that the boundary isotopy headline consumes: on an immersed
family of embedded loops, smooth on the closed time window, the temporal velocity field extends
to a global smooth time dependent vector field whose one sided time derivatives reproduce the
family on the window. -/
def LoopFamilyVelocityExtensionProducer (a b : ℝ) : Prop :=
  ∀ γ : ℝ → ContinuousFreeLoop M,
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
    (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
    (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
    LoopFamilyVelocityExtension (I := I) a b γ

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_velocityExtensionProducer
    (h : LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z :=
  let _ := hab
  rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀ (h γ hγ hi hemb)

omit [CompleteSpace E] [FiniteDimensional ℝ E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionProducer_of_allWindows
    (h : ∀ (a' b' : ℝ) (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a' b') →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a' b') →
      (∀ t ∈ Icc a' b', Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtension (I := I) a' b' γ) :
    LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  fun γ hγ hi hemb => h a b γ hγ hi hemb

end Manifold

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

/-- The remaining genuinely analytic gap of the model space producer: a family that is only
smooth on the closed time window has to be replaced by a globally smooth family with the same
values on the window and with injective graph lift derivative. -/
def LoopFamilyGlobalSmoothExtension (a b : ℝ) (γ : ℝ → ContinuousFreeLoop E) : Prop :=
  ∃ γ' : ℝ → ContinuousFreeLoop E,
    (∀ t ∈ Icc a b, γ' t = γ t) ∧
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ' q.1 (q.2 : Surgery.Topology.Circle)) ∧
    (∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ' t z)) ∧
    ∀ q, Function.Injective (fderiv ℝ (graphLift γ') q)

omit [FiniteDimensional ℝ E] in
theorem loopFamilyGlobalSmoothExtension_of_globalSmooth
    {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (hemb : ∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : ∀ q, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    LoopFamilyGlobalSmoothExtension a b γ :=
  ⟨γ, fun _ _ => rfl, hγ, hemb, hi⟩

theorem loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension
    {γ : ℝ → ContinuousFreeLoop E} (h : LoopFamilyGlobalSmoothExtension a b γ) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ := by
  obtain ⟨γ', hagree, hγ', hemb', hi'⟩ := h
  obtain ⟨X, hX, hIco, hIoc⟩ := loopFamilyVelocityExtension_modelSpace a b γ' hemb' hγ' hi'
  refine ⟨X, hX, ?_, ?_⟩
  · intro t ht z
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hsub : Iio (t + (b - t)) ∩ Ici t ⊆ Icc a b := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨le_trans ht.1 hs2, ?_⟩
      have : s < b := by
        have h1 : t + (b - t) = b := by ring
        rwa [h1] at hs1
      exact this.le
    have hmem : Icc a b ∈ 𝓝[Ici t] t :=
      mem_of_superset
        (inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by
            have h1 : t + (b - t) = b := by ring
            rw [h1]; exact ht.2)))
          self_mem_nhdsWithin) hsub
    have heq : (fun s : ℝ => γ s z) =ᶠ[𝓝[Ici t] t] (fun s : ℝ => γ' s z) :=
      eventually_of_mem hmem fun s hs =>
        (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree s hs)).symm
    have hx : γ t z = γ' t z :=
      (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree t htIcc)).symm
    have hbase := hIco t ht z
    rw [show X t (γ' t z) = X t (γ t z) from by rw [hx]] at hbase
    exact hbase.congr_of_eventuallyEq heq hx
  · intro t ht z
    have htIcc : t ∈ Icc a b := Ioc_subset_Icc_self ht
    have hsub : Ioi (t - (t - a)) ∩ Iic t ⊆ Icc a b := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨?_, le_trans hs2 ht.2⟩
      have : a < s := by
        have h1 : t - (t - a) = a := by ring
        rwa [h1] at hs1
      exact this.le
    have hmem : Icc a b ∈ 𝓝[Iic t] t :=
      mem_of_superset
        (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by
            have h1 : t - (t - a) = a := by ring
            rw [h1]; exact ht.1)))
          self_mem_nhdsWithin) hsub
    have heq : (fun s : ℝ => γ s z) =ᶠ[𝓝[Iic t] t] (fun s : ℝ => γ' s z) :=
      eventually_of_mem hmem fun s hs =>
        (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree s hs)).symm
    have hx : γ t z = γ' t z :=
      (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree t htIcc)).symm
    have hbase := hIoc t ht z
    rw [show X t (γ' t z) = X t (γ t z) from by rw [hx]] at hbase
    exact hbase.congr_of_eventuallyEq heq hx

end ModelSpace

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
