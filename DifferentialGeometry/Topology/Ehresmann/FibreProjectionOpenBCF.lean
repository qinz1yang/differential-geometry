import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic

/-!
# The restriction of a product-chart map to the preimage of a base subset is open (lane S-BCF03)

Kernel of `circle_base` of `EmbeddedFacePartition_BCF` (a circle bundle over a circle projects
openly): if `f : Wt → H` has, over every point `y` of `C ⊆ Bs`, a local product chart
`φ : E × Q → Wt` (continuous, `range φ = X ∩ f⁻¹(range σ)`, `f (φ (x, z)) = σ x`) over a topological
embedding `σ : E → H` with `range σ = Bs ∩ O` (`O` open), then `f` restricted to
`Σ = X ∩ f⁻¹ C` sends relatively open sets of `Σ` to relatively open sets of `C`.

* `exists_open_image_fibreProj_BCF`: for an open `U' ⊆ Wt`, `f '' (Σ ∩ U') = V ∩ C` with `V` open;
* `isOpenMap_restrict_fibreProj_BCF`: the restriction `Σ → C` is an open map.
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology

variable {E Q Wt H : Type*} [TopologicalSpace E] [TopologicalSpace Q] [TopologicalSpace Wt]
  [TopologicalSpace H]

/-- **Local step**: a point `q ∈ Σ ∩ U'` has an open `V ∋ f q` with `V ∩ C ⊆ f '' (Σ ∩ U')`. -/
theorem exists_open_nbhd_image_fibreProj_BCF {X : Set Wt} {f : Wt → H} {Bs C : Set H}
    (hCB : C ⊆ Bs)
    (hchart : ∀ y ∈ C, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E), σ x₀ = y ∧
      IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x)
    {U' : Set Wt} (hU' : IsOpen U') {q : Wt} (hq : q ∈ (X ∩ f ⁻¹' C) ∩ U') :
    ∃ V : Set H, IsOpen V ∧ f q ∈ V ∧ V ∩ C ⊆ f '' ((X ∩ f ⁻¹' C) ∩ U') := by
  obtain ⟨⟨hqX, hqC⟩, hqU⟩ := hq
  obtain ⟨σ, φ, O, x₀, hx₀, hσ, hO, hσr, hφc, hφr, hφf⟩ := hchart (f q) hqC
  have hqr : q ∈ range φ := by
    rw [hφr]
    exact ⟨hqX, ⟨x₀, hx₀⟩⟩
  obtain ⟨⟨x₁, z₁⟩, rfl⟩ := hqr
  have hopen : IsOpen (φ ⁻¹' U') := hU'.preimage hφc
  obtain ⟨N, M, hN, hM, hx₁N, hz₁M, hsub⟩ := isOpen_prod_iff.mp hopen x₁ z₁ hqU
  -- `σ '' N` is relatively open in `range σ`
  obtain ⟨V₀, hV₀, hV₀N⟩ := hσ.isInducing.isOpen_iff.mp hN
  have hV₀' : V₀ ∩ range σ = σ '' N := by
    ext y
    constructor
    · rintro ⟨hy, x, rfl⟩
      exact ⟨x, by rw [← hV₀N]; exact hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by have := hV₀N ▸ hx; exact this, x, rfl⟩
  refine ⟨V₀ ∩ O, hV₀.inter hO, ⟨?_, ?_⟩, ?_⟩
  · have : σ x₁ ∈ V₀ ∩ range σ := by
      rw [hV₀']
      exact ⟨x₁, hx₁N, rfl⟩
    rw [hφf x₁ z₁]
    exact this.1
  · rw [hφf x₁ z₁]
    have : σ x₁ ∈ range σ := mem_range_self x₁
    rw [hσr] at this
    exact this.2
  · rintro y ⟨⟨hyV, hyO⟩, hyC⟩
    have hyr : y ∈ range σ := by
      rw [hσr]
      exact ⟨hCB hyC, hyO⟩
    have hyN : y ∈ σ '' N := by
      rw [← hV₀']
      exact ⟨hyV, hyr⟩
    obtain ⟨x, hxN, rfl⟩ := hyN
    refine ⟨φ (x, z₁), ⟨⟨?_, ?_⟩, ?_⟩, hφf x z₁⟩
    · have : φ (x, z₁) ∈ range φ := mem_range_self _
      rw [hφr] at this
      exact this.1
    · change f (φ (x, z₁)) ∈ C
      rw [hφf x z₁]
      exact hyC
    · exact hsub ⟨hxN, hz₁M⟩

/-- **The image of a relatively open set of `Σ = X ∩ f⁻¹ C` is relatively open in `C`.** -/
theorem exists_open_image_fibreProj_BCF {X : Set Wt} {f : Wt → H} {Bs C : Set H}
    (hCB : C ⊆ Bs)
    (hchart : ∀ y ∈ C, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E), σ x₀ = y ∧
      IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x)
    {U' : Set Wt} (hU' : IsOpen U') :
    ∃ V : Set H, IsOpen V ∧ V ∩ C = f '' ((X ∩ f ⁻¹' C) ∩ U') := by
  choose! V hVo hqV hVsub using fun q (hq : q ∈ (X ∩ f ⁻¹' C) ∩ U') =>
    exists_open_nbhd_image_fibreProj_BCF hCB hchart hU' hq
  refine ⟨⋃ q ∈ (X ∩ f ⁻¹' C) ∩ U', V q, isOpen_biUnion fun q hq => hVo q hq, ?_⟩
  ext y
  constructor
  · rintro ⟨hyV, hyC⟩
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hyV
    exact hVsub q hq ⟨hyq, hyC⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨mem_biUnion hq (hqV q hq), hq.1.2⟩

/-- **The restriction `Σ → C` is an open map** (the form of `circle_base`). -/
theorem isOpenMap_restrict_fibreProj_BCF {X : Set Wt} {f : Wt → H} {Bs C : Set H}
    (hCB : C ⊆ Bs)
    (hchart : ∀ y ∈ C, ∃ (σ : E → H) (φ : E × Q → Wt) (O : Set H) (x₀ : E), σ x₀ = y ∧
      IsEmbedding σ ∧ IsOpen O ∧ range σ = Bs ∩ O ∧ Continuous φ ∧
      range φ = X ∩ f ⁻¹' range σ ∧ ∀ x z, f (φ (x, z)) = σ x) :
    IsOpenMap (fun q : (X ∩ f ⁻¹' C : Set Wt) => (⟨f q, q.2.2⟩ : C)) := by
  intro G hG
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.mp hG
  obtain ⟨V, hV, hVeq⟩ := exists_open_image_fibreProj_BCF hCB hchart (X := X) (f := f) hU'
  have : (fun q : (X ∩ f ⁻¹' C : Set Wt) => (⟨f q, q.2.2⟩ : C)) '' (Subtype.val ⁻¹' U') =
      Subtype.val ⁻¹' V := by
    ext ⟨y, hyC⟩
    constructor
    · rintro ⟨q, hq, hqy⟩
      have h1 : f q = y := congrArg Subtype.val hqy
      have : y ∈ V ∩ C := by
        rw [hVeq]
        exact ⟨q.1, ⟨q.2, hq⟩, h1⟩
      exact this.1
    · intro hyV
      have : y ∈ f '' ((X ∩ f ⁻¹' C) ∩ U') := by
        rw [← hVeq]
        exact ⟨hyV, hyC⟩
      obtain ⟨q, ⟨hqS, hqU⟩, hqy⟩ := this
      exact ⟨⟨q, hqS⟩, hqU, Subtype.ext hqy⟩
  rw [this]
  exact hV.preimage continuous_subtype_val

end DifferentialGeometry.Topology
