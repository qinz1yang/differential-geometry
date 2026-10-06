import DifferentialGeometry.Topology.Ehresmann.BundleOverArcBCF
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Circle charts over an arc glue to an annulus parametrization (lane S-BCF03b)

Assembly kernel of `annulus_param` of `EmbeddedFacePartition_BCF` (BCF03 G7, P6), on top of the
arc kernel of G21 (`exists_bundle_trivialization_over_arc_BCF`):

* `circleSphereHomeomorph_BCF`: `Circle ≃ₜ Metric.sphere (0 : ℝ²) 1`;
* `exists_localTriv_over_arc_BCF`: over a continuous injective arc `a : [0, 1] → Bs`, a family of
  local product charts `φ : E × Q → Wt` over topological embeddings `σ : E → H` (with
  `range σ = Bs ∩ O`) gives the local trivializations `τ (z, s) = φ (σ⁻¹ (a s), z)` demanded by
  `hloc` of the arc kernel;
* `exists_annulus_param_BCF`: the resulting parametrization `e : S¹ × [0, 1] → Wt`: continuous,
  injective, `range e = X ∩ f⁻¹(a [0, 1])`, `f (e (z, s)) = a s`, and the end circles
  `e '' {s = 0} = X ∩ f⁻¹{a 0}`, `e '' {s = 1} = X ∩ f⁻¹{a 1}` are the WHOLE fibres over the ends.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology

/-- The standard homeomorphism between the unit circle of `ℂ` (`Circle`) and the unit sphere of
the Euclidean plane. -/
def circleSphereHomeomorph_BCF : Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]

section Arc

variable {E Q Wt H : Type*} [TopologicalSpace E] [TopologicalSpace Q] [TopologicalSpace Wt]
  [TopologicalSpace H] {X : Set Wt} {f : Wt → H} {Bs : Set H} {a : ℝ → H}

/-- **Local trivializations of a family of product charts over an injective arc.** -/
theorem exists_localTriv_over_arc_BCF (ha : ContinuousOn a (Icc 0 1)) (hai : InjOn a (Icc 0 1))
    (haB : a '' Icc 0 1 ⊆ Bs)
    (hchart : ∀ y ∈ a '' Icc 0 1, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ ∃ τ : Q × ℝ → Wt,
      ContinuousOn τ (univ ×ˢ (U ∩ Icc 0 1)) ∧ InjOn τ (univ ×ˢ (U ∩ Icc 0 1)) ∧
      (∀ z, ∀ s ∈ U ∩ Icc (0 : ℝ) 1, f (τ (z, s)) = a s) ∧
      τ '' (univ ×ˢ (U ∩ Icc 0 1)) = X ∩ f ⁻¹' (a '' (U ∩ Icc 0 1)) := by
  classical
  intro t ht
  obtain ⟨σ, φ, O, x₀, hx₀, hσ, hO, hσr, hφc, hφi, hφr, hφf⟩ := hchart (a t) ⟨t, ht, rfl⟩
  have hat : a t ∈ range σ := ⟨x₀, hx₀⟩
  have hatO : a t ∈ O := (hσr ▸ hat : a t ∈ Bs ∩ O).2
  have hpre : a ⁻¹' O ∈ 𝓝[Icc 0 1] t := (ha t ht).preimage_mem_nhdsWithin (hO.mem_nhds hatO)
  obtain ⟨U, hU, htU, hUO⟩ := mem_nhdsWithin.mp hpre
  have hmem : ∀ s ∈ U ∩ Icc (0 : ℝ) 1, a s ∈ range σ := fun s hs =>
    hσr ▸ ⟨haB ⟨s, hs.2, rfl⟩, hUO hs⟩
  let g : E ≃ₜ range σ := hσ.toHomeomorph
  let ρ : ℝ → E := fun s => if h : a s ∈ range σ then g.symm ⟨a s, h⟩ else x₀
  have hρσ : ∀ s ∈ U ∩ Icc (0 : ℝ) 1, σ (ρ s) = a s := by
    intro s hs
    have h := hmem s hs
    have : ρ s = g.symm ⟨a s, h⟩ := by simp only [ρ, h, ↓reduceDIte]
    rw [this]
    have h2 := congrArg Subtype.val (g.apply_symm_apply ⟨a s, h⟩)
    exact h2
  have hρc : ContinuousOn ρ (U ∩ Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : Continuous ((U ∩ Icc (0 : ℝ) 1).domRestrict a) :=
      (ha.mono inter_subset_right).domRestrict
    have h2 : Continuous fun s : (U ∩ Icc (0 : ℝ) 1 : Set ℝ) =>
        g.symm ⟨a s, hmem s s.2⟩ := g.symm.continuous.comp (h1.subtype_mk _)
    refine h2.congr fun s => ?_
    have h := hmem s s.2
    change g.symm ⟨a s, h⟩ = ρ s
    simp only [ρ, h, ↓reduceDIte]
  refine ⟨U, hU, htU, fun p => φ (ρ p.2, p.1), ?_, ?_, ?_, ?_⟩
  · refine hφc.comp_continuousOn (ContinuousOn.prodMk ?_ continuousOn_fst)
    exact hρc.comp continuousOn_snd fun p hp => hp.2
  · rintro ⟨z, s⟩ ⟨-, hs⟩ ⟨z', s'⟩ ⟨-, hs'⟩ hzs
    have h1 := hφi hzs
    have hz : z = z' := (Prod.mk.inj h1).2
    have hρ' : ρ s = ρ s' := (Prod.mk.inj h1).1
    have hss : a s = a s' := by rw [← hρσ s hs, ← hρσ s' hs', hρ']
    exact Prod.ext hz (hai hs.2 hs'.2 hss)
  · intro z s hs
    change f (φ (ρ s, z)) = a s
    rw [hφf, hρσ s hs]
  · ext p
    constructor
    · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
      have hr : φ (ρ s, z) ∈ range φ := mem_range_self _
      rw [hφr] at hr
      refine ⟨hr.1, s, hs, ?_⟩
      change a s = f (φ (ρ s, z))
      rw [hφf, hρσ s hs]
    · rintro ⟨hpX, s, hs, hps⟩
      have hpr : p ∈ range φ := by
        rw [hφr]
        exact ⟨hpX, by rw [mem_preimage, ← hps]; exact hmem s hs⟩
      obtain ⟨⟨x, z⟩, rfl⟩ := hpr
      have hxs : σ x = a s := by rw [← hφf x z]; exact hps.symm
      have hxρ : x = ρ s := hσ.injective (by rw [hxs, hρσ s hs])
      exact ⟨(z, s), ⟨mem_univ _, hs⟩, by simp [hxρ]⟩

variable [CompactSpace Q] [Nonempty Q] [T2Space Wt]

/-- **The annulus parametrization over an arc of the base** (kernel of `annulus_param`). -/
theorem exists_annulus_param_BCF (ha : ContinuousOn a (Icc 0 1)) (hai : InjOn a (Icc 0 1))
    (haB : a '' Icc 0 1 ⊆ Bs)
    (hchart : ∀ y ∈ a '' Icc 0 1, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧ Injective φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x) :
    ∃ e : Q × Icc (0 : ℝ) 1 → Wt, Continuous e ∧ Injective e ∧
      range e = X ∩ f ⁻¹' (a '' Icc 0 1) ∧ (∀ q, f (e q) = a q.2) ∧
      e '' {q | (q.2 : ℝ) = 0} = X ∩ f ⁻¹' {a 0} ∧
      e '' {q | (q.2 : ℝ) = 1} = X ∩ f ⁻¹' {a 1} := by
  obtain ⟨F, hFc, hFi, hFπ, hFim⟩ := exists_bundle_trivialization_over_arc_BCF (π := f) (P := X)
    hai (exists_localTriv_over_arc_BCF ha hai haB hchart)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hslice : ∀ b ∈ Icc (0 : ℝ) 1, F '' (univ ×ˢ {b}) = X ∩ f ⁻¹' {a b} := fun b hb =>
    image_slice_BCF (π := f) (P := X) hai subset_rfl hFπ hFim hb
  let e : Q × Icc (0 : ℝ) 1 → Wt := fun q => F (q.1, q.2)
  have hcont : Continuous e := by
    have h := hFc.comp_continuous (f := fun q : Q × Icc (0 : ℝ) 1 => ((q.1, (q.2 : ℝ)) : Q × ℝ))
      (by fun_prop) fun q => ⟨mem_univ _, q.2.2⟩
    exact h
  refine ⟨e, hcont, ?_, ?_, ?_, ?_, ?_⟩
  · intro q q' hqq'
    have := hFi ⟨mem_univ _, q.2.2⟩ ⟨mem_univ _, q'.2.2⟩ hqq'
    exact Prod.ext (Prod.mk.inj this).1 (Subtype.ext (Prod.mk.inj this).2)
  · rw [← hFim]
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q.1, q.2), ⟨mem_univ _, q.2.2⟩, rfl⟩
    · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
      exact ⟨(z, ⟨s, hs⟩), rfl⟩
  · exact fun q => hFπ q.1 q.2 q.2.2
  · rw [← hslice 0 h0]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q.1, q.2), ⟨mem_univ _, hq⟩, rfl⟩
    · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
      have hs0 : s = 0 := hs
      exact ⟨(z, ⟨s, by rw [hs0]; exact h0⟩), by simp [hs0], rfl⟩
  · rw [← hslice 1 h1]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q.1, q.2), ⟨mem_univ _, hq⟩, rfl⟩
    · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩
      have hs0 : s = 1 := hs
      exact ⟨(z, ⟨s, by rw [hs0]; exact h1⟩), by simp [hs0], rfl⟩

end Arc

end DifferentialGeometry.Topology
