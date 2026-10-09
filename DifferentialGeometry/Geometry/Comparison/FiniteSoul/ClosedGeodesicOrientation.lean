import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicNormal
import DifferentialGeometry.Topology.Manifold.Orientation
import DifferentialGeometry.Bundle.Orientation.BasisContinuity

/-!
# Trivial holonomy of the unit normal on an oriented surface (S-TUBE, D3: σ = 1)

Package CM-S (finite soul), lane CMS-T. On a surface with a `ManifoldOrientation`, a continuous unit
normal `ν` along a closed unit geodesic of period `ℓ` is periodic: `ν (t + ℓ) = ν t`
(`holonomy_eq_one_of_orientation`). Proof: the orientation of the frame `(γ'(t), ν(t))`
relative to the orientation of `M` is locally constant (in a bundle chart both the chart frame and
the chart reading of the orientation are locally constant), hence constant; the frame at `t + ℓ`
is `(γ'(t), σ ν(t))`, of orientation `σ` times that at `t`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An orthonormal pair for a bilinear form is linearly independent. -/
theorem linearIndependent_pair_of_orthonormal {B : E →L[ℝ] E →L[ℝ] ℝ} {U N : E}
    (hU : B U U = 1) (hN : B N N = 1) (hNU : B N U = 0) (hUN : B U N = 0) :
    LinearIndependent ℝ ![U, N] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun z => B z U) hst
  have h2 := congrArg (fun z => B z N) hst
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, map_zero, zero_apply, hU, hN,
    hNU, hUN] at h1 h2
  constructor <;> linarith

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **σ = 1 on an oriented surface**: the holonomy sign of a continuous unit normal along a closed
unit geodesic is `1`. -/
theorem holonomy_eq_one_of_orientation
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (hdom : g.geodesicFlowDomain = univ) (hdim : Module.finrank ℝ E = 2)
    (p : TangentBundle I M) {ℓ : ℝ} (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p) {ν : ℝ → E}
    (hν : Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)))
    (hνunit : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1)
    (hνperp : ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0)
    (o : DifferentialGeometry.ManifoldOrientation I M 2) {σ : ℤˣ}
    (hσ : ∀ t, ν (t + ℓ) = ((σ : ℤ) : ℝ) • ν t) : σ = 1 := by
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hdom]; exact mem_univ q
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγ
  set U : ℝ → E := fun t => (g.geodesicFlow p t).snd with hU
  have hflc : Continuous fun t => g.geodesicFlow p t := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hin : ContMDiff 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (p, s)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (((g.contMDiffOn_geodesicFlow hr).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hmem _))).comp t
      ((hin t).of_le (by exact_mod_cast le_top))).continuousAt
  have hγc : Continuous γ :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp hflc
  -- the frame `(γ', ν)`
  have hli : ∀ t, LinearIndependent ℝ ![U t, ν t] := by
    intro t
    set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (γ t) with hB
    have h1 : B (U t) (U t) = 1 := by
      change g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd
        (g.geodesicFlow p t).snd = 1
      rw [g.inner_geodesicFlow_eq hr p t (hmem _), hunit]
    have h2 : B (ν t) (ν t) = 1 := hνunit t
    have h3 : B (ν t) (U t) = 0 := hνperp t
    have h4 : B (U t) (ν t) = 0 := (g.symm _ _ _).trans (hνperp t)
    exact linearIndependent_pair_of_orthonormal h1 h2 h3 h4
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ E := by rw [hdim, Fintype.card_fin]
  set b : ℝ → Module.Basis (Fin 2) ℝ E := fun t =>
    basisOfLinearIndependentOfCardEqFinrank (hli t) hcard with hb
  have hbapp : ∀ t i, b t i = ![U t, ν t] i := fun t i => by
    simp only [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  set s : ℝ → Prop := fun t => (b t).orientation = (o.orientation (γ t) : Orientation ℝ E (Fin 2))
    with hs
  -- local constancy of `s`
  have hloc : ∀ t₀, ∀ᶠ t in 𝓝 t₀, s t = s t₀ := by
    intro t₀
    set x₀ := γ t₀ with hx₀def
    set T := trivializationAt E (TangentSpace I : M → Type _) x₀ with hT
    have hx₀ : x₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    obtain ⟨V, hVo, hx₀V, hVsub, hconst⟩ := o.locally_constant x₀ x₀ hx₀
    set X : Set ℝ := γ ⁻¹' V with hX
    have hXo : IsOpen X := hVo.preimage hγc
    have ht₀X : t₀ ∈ X := hx₀V
    let L : X → (E ≃ₗ[ℝ] E) := fun t =>
      DifferentialGeometry.tangentChartEquiv I M x₀ (γ t) (hVsub t.2)
    let c : X → Module.Basis (Fin 2) ℝ E := fun t => (b t).map (L t)
    have hcapp : ∀ (t : X) (i : Fin 2), c t i =
        (T (⟨γ t, ![U t, ν t] i⟩ : TangentBundle I M)).2 := by
      intro t i
      change L t (b t i) = _
      rw [hbapp]
      exact Trivialization.linearEquivAt_apply (R := ℝ) T (γ t) (hVsub t.2) _
    have hcvec : ∀ i, Continuous fun t : X => c t i := by
      intro i
      have hcurve : Continuous fun t : X => (⟨γ t, ![U t, ν t] i⟩ : TangentBundle I M) := by
        fin_cases i
        · exact hflc.comp continuous_subtype_val
        · exact hν.comp continuous_subtype_val
      have hT : Continuous fun t : X => T (⟨γ t, ![U t, ν t] i⟩ : TangentBundle I M) :=
        T.continuousOn.comp_continuous hcurve fun t => by
          rw [T.mem_source]; exact hVsub t.2
      exact (continuous_snd.comp hT).congr fun t => (hcapp t i).symm
    let _ := DifferentialGeometry.VectorBundle.orientationTopology (V := E) (n := 2)
    have hdisc : DiscreteTopology (Orientation ℝ E (Fin 2)) := ⟨rfl⟩
    have hcc := DifferentialGeometry.VectorBundle.continuous_basis_orientation hdim c hcvec
    set t₀' : X := ⟨t₀, ht₀X⟩ with ht₀'
    set W : Set X := (fun t => (c t).orientation) ⁻¹' {(c t₀').orientation} with hW
    have hWo : IsOpen W := hcc.isOpen_preimage _ (isOpen_discrete _)
    have hWℝ : IsOpen (Subtype.val '' W) := hXo.isOpenMap_subtype_val W hWo
    filter_upwards [hWℝ.mem_nhds ⟨t₀', rfl, rfl⟩] with t ht
    obtain ⟨t', ht'W, rfl⟩ := ht
    -- `s` read in the chart
    have hread : ∀ t'' : X, s t'' = ((c t'').orientation =
        Orientation.map (Fin 2) (DifferentialGeometry.tangentChartEquiv I M x₀ x₀ hx₀)
          (o.orientation x₀)) := by
      intro t''
      rw [← hconst (γ t'') t''.2]
      apply propext
      change (b t'').orientation = (o.orientation (γ t'') : Orientation ℝ E (Fin 2)) ↔ _
      rw [Module.Basis.orientation_map]
      exact (Orientation.map (Fin 2) (L t'')).injective.eq_iff.symm
    have h1 := hread t'
    have h2 := hread t₀'
    have hcw : (c t').orientation = (c t₀').orientation := ht'W
    rw [h1, h2, hcw]
  -- `s` is constant
  have hlc : IsLocallyConstant s := (IsLocallyConstant.iff_eventually_eq s).mpr hloc
  have hsℓ : s ℓ = s 0 := hlc.apply_eq_of_preconnectedSpace ℓ 0
  -- the frame after one period
  have hP : g.geodesicFlow p ℓ = g.geodesicFlow p 0 := by
    rw [g.geodesicFlow_zero hr]; exact hper
  have hγℓ : γ ℓ = γ 0 := congrArg Bundle.TotalSpace.proj hP
  have hUℓ : U ℓ = U 0 := congrArg (fun q : TangentBundle I M => (q.snd : E)) hP
  have hνℓ : ν ℓ = ((σ : ℤ) : ℝ) • ν 0 := by simpa using hσ 0
  have hoℓ : (o.orientation (γ ℓ) : Orientation ℝ E (Fin 2)) = o.orientation (γ 0) := by
    have key : ∀ x y : M, x = y →
        (o.orientation x : Orientation ℝ E (Fin 2)) = o.orientation y := by
      rintro x y rfl; rfl
    exact key _ _ hγℓ
  rcases Int.units_eq_one_or σ with h | h
  · exact h
  exfalso
  rw [h] at hνℓ
  have hbℓ : b ℓ = (b 0).unitsSMul (Function.update 1 1 (-1)) := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [Module.Basis.unitsSMul_apply, hbapp, hbapp]
    fin_cases i
    · simp [hUℓ]
    · simp [hνℓ]
  have hor : (b ℓ).orientation = -(b 0).orientation := by
    rw [hbℓ, Module.Basis.orientation_neg_single]
  have hs0 : s ℓ ↔ s 0 := by rw [hsℓ]
  change (b ℓ).orientation = (o.orientation (γ ℓ) : Orientation ℝ E (Fin 2)) ↔
    (b 0).orientation = (o.orientation (γ 0) : Orientation ℝ E (Fin 2)) at hs0
  rw [hor, hoℓ] at hs0
  set O₀ : Orientation ℝ E (Fin 2) := o.orientation (γ 0) with hO₀
  rcases (b 0).orientation_eq_or_eq_neg O₀ with h0 | h0
  · have h' := hs0.mpr h0.symm
    rw [← h0] at h'
    exact Module.Ray.ne_neg_self O₀ h'.symm
  · have h' := hs0.mp h0.symm
    rw [h'] at h0
    exact Module.Ray.ne_neg_self O₀ h0

end DifferentialGeometry.Geometry.FiniteSoul
