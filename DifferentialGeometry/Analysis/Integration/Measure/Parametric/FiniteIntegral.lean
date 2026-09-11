import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations

universe u v w

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Integral.Measure

theorem hasFDerivAt_integral_compactOn
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    {U : Set V} (hU : IsOpen U)
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : ContinuousOn (fun p : V × X => F p.1 p.2) (U ×ˢ (Set.univ : Set X)))
    (hF' : ContinuousOn (fun p : V × X => F' p.1 p.2) (U ×ˢ (Set.univ : Set X)))
    (hdiff : ∀ u : V, u ∈ U → ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) (hu : u ∈ U) :
    HasFDerivAt (fun v : V => ∫ x, F v x ∂μ) (∫ x, F' u x ∂μ) u := by
  have hslice (v : V) (hv : v ∈ U) : Continuous (F v) := by
    rw [← continuousOn_univ]
    exact hF.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨hv, mem_univ x⟩)
  have hslice' : Continuous (F' u) := by
    rw [← continuousOn_univ]
    exact hF'.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨hu, mem_univ x⟩)
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_bound_of_continuousOn
    hslice'.continuousOn
  let A := (U ×ˢ (univ : Set X)) ∩
    (fun p : V × X => ‖F' p.1 p.2‖) ⁻¹' Iio (C + 1)
  have hA : IsOpen A :=
    hF'.norm.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_Iio
  have hsub : ({u} : Set V) ×ˢ (univ : Set X) ⊆ A := by
    rintro ⟨v, x⟩ ⟨rfl, hx⟩
    exact ⟨⟨hu, hx⟩, (hC x hx).trans_lt (lt_add_one C)⟩
  obtain ⟨S, T, hS, _, huS, hT, hST⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hA hsub
  have hnear : S ∩ U ∈ 𝓝 u :=
    (hS.inter hU).mem_nhds ⟨singleton_subset_iff.mp huS, hu⟩
  have hmeas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) μ := by
    filter_upwards [hnear] with v hv
    exact (hslice v hv.2).aestronglyMeasurable
  have hint : Integrable (F u) μ :=
    integrableOn_univ.mp ((hslice u hu).continuousOn.integrableOn_compact isCompact_univ)
  have hbound : ∀ᵐ x ∂μ, ∀ v ∈ S ∩ U, ‖F' v x‖ ≤ C + 1 := by
    filter_upwards [] with x
    intro v hv
    exact le_of_lt (hST (show (v, x) ∈ S ×ˢ T from ⟨hv.1, hT (mem_univ x)⟩)).2
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hnear hmeas hint
    hslice'.aestronglyMeasurable hbound (integrable_const (C + 1))
    (Filter.Eventually.of_forall fun x v hv => hdiff v hv.2 x)

theorem hasFDerivAt_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    HasFDerivAt (fun v : V => ∫ x, F v x ∂μ) (∫ x, F' u x ∂μ) u := by
  exact hasFDerivAt_integral_compactOn μ isOpen_univ F F' hF.continuousOn hF'.continuousOn
    (fun v _ x => hdiff v x) u (mem_univ u)

theorem fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u = ∫ x, F' u x ∂μ :=
  (hasFDerivAt_integral_compact μ F F' hF hF' hdiff u).fderiv

theorem continuous_fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (F'' : V → X → (V →L[ℝ] (V →L[ℝ] W)))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hF'' : Continuous (fun p : V × X => F'' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (hdiff' : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F' v x) (F'' u x) u) :
    Continuous (fun u : V => fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u) := by
  let D : V → (V →L[ℝ] W) := fun u => ∫ x, F' u x ∂μ
  have hDdiff : Differentiable ℝ D := by
    intro u
    exact (hasFDerivAt_integral_compact μ F' F'' hF' hF'' hdiff' u).differentiableAt
  have hEq : (fun u : V => fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u) = D := by
    funext u
    exact fderiv_integral_compact μ F F' hF hF' hdiff u
  rw [hEq]
  exact hDdiff.continuous

private theorem contDiffOn_integral_subtype_of_isCompact_nat
    {V : Type u} {X : Type w} {F : Type (max u v)}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) {K : Set X} (hK : IsCompact K)
    (μ : Measure K) [IsFiniteMeasure μ] {U : Set V} {Ω : Set (V × X)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hsub : U ×ˢ K ⊆ Ω)
    {f : V × X → F} (hf : ContDiffOn ℝ n f Ω) :
    ContDiffOn ℝ n (fun v => ∫ s : K, f (v, s) ∂μ) U := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  induction n generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    apply continuousOn_integral_of_compact_support (μ := μ)
      (isCompact_univ : IsCompact (univ : Set K))
    · exact hf.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
    · intro _ s _ hs
      exact (hs (mem_univ s)).elim
  | succ n ih =>
    rw [Nat.cast_succ] at hf ⊢
    let D : V × X → V →L[ℝ] F := fun z =>
      (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ V X)
    have hD : ContDiffOn ℝ n D Ω :=
      (hf.fderiv_of_isOpen hΩ le_rfl).clm_comp contDiffOn_const
    have hd (v : V) (hv : v ∈ U) :
        HasFDerivAt (fun v => ∫ s : K, f (v, s) ∂μ)
          (∫ s : K, D (v, s) ∂μ) v := by
      apply hasFDerivAt_integral_compactOn μ hU
        (fun v (s : K) => f (v, s))
        (fun v (s : K) => D (v, s))
      · exact hf.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
      · exact hD.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
      · intro w hw s
        have hdf := (hf.one_of_succ.differentiableOn one_ne_zero _
          (hsub (show (w, (s : X)) ∈ U ×ˢ K from ⟨hw, s.property⟩))).differentiableAt
          (hΩ.mem_nhds (hsub (show (w, (s : X)) ∈ U ×ˢ K from ⟨hw, s.property⟩)))
        exact hdf.hasFDerivAt.comp w
          ((hasFDerivAt_id w).prodMk (hasFDerivAt_const (s : X) w))
      · exact hv
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun v hv => (hd v hv).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih hD).congr (fun v hv => (hd v hv).fderiv)

theorem contDiffOn_integral_subtype_of_isCompact
    {V : Type u} {X : Type w} {F : Type v}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ∞) {K : Set X} (hK : IsCompact K)
    (μ : Measure K) [IsFiniteMeasure μ] {U : Set V} {Ω : Set (V × X)}
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hsub : U ×ˢ K ⊆ Ω) {f : V × X → F}
    (hf : ContDiffOn ℝ n f Ω) :
    ContDiffOn ℝ n (fun v => ∫ s : K, f (v, s) ∂μ) U := by
  suffices hnat : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContDiffOn ℝ m
      (fun v => ∫ s : K, f (v, s) ∂μ) U by
    cases n using ENat.recTopCoe with
    | top => exact contDiffOn_infty.mpr (fun m => hnat m le_top)
    | coe m => exact hnat m le_rfl
  intro m hm
  let L : ULift.{u} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  have hlift : ContDiffOn ℝ m (fun z => L.symm (f z)) Ω :=
    L.symm.contDiff.comp_contDiffOn (hf.of_le (by exact_mod_cast hm))
  have hi := contDiffOn_integral_subtype_of_isCompact_nat m hK μ hU hΩ hsub hlift
  have h := L.contDiff.comp_contDiffOn hi
  apply h.congr
  intro x _
  simp only [Function.comp_apply, ← L.integral_comp_comm, L.apply_symm_apply]

end DifferentialGeometry.Integral.Measure

end
