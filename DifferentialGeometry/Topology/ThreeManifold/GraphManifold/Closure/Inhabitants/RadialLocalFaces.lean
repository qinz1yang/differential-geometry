import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialFibreFaces

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

theorem radial_cbase_iff {b : radialCircleBase} : b ∈ radialCircleBundle.cbase ↔
    ∀ l : Fin 2, radialCircleDefining l b ≤ 0 := by
  change b ∈ radialCircleCornerBase ↔ _
  rw [radialCircleCornerBase_eq]
  rfl

theorem radial_frontier_active (b : radialCircleBase)
    (hb : b ∈ frontier radialCircleBundle.cbase) :
    ∃ l : Fin 2, radialCircleDefining l b = 0 := by
  have hm : b ∈ radialCircleBundle.cbase :=
    radialCircleCornerBase_compact.isClosed.frontier_subset hb
  have hle := radial_cbase_iff.mp hm
  by_cases h0 : radialCircleDefining (0 : Fin 2) b = 0
  · exact ⟨0, h0⟩
  by_cases h1 : radialCircleDefining (1 : Fin 2) b = 0
  · exact ⟨1, h1⟩
  have hs0 : radialCircleDefining (0 : Fin 2) b < 0 := by
    rcases (hle 0).eq_or_lt with h | h
    · exact (h0 h).elim
    · exact h
  have hs1 : radialCircleDefining (1 : Fin 2) b < 0 := by
    rcases (hle 1).eq_or_lt with h | h
    · exact (h1 h).elim
    · exact h
  have ho : IsOpen {c : radialCircleBase | radialCircleDefining 0 c < 0 ∧
      radialCircleDefining 1 c < 0} :=
    (isOpen_lt (radialCircleDefining_smooth 0).continuous continuous_const).inter
      (isOpen_lt (radialCircleDefining_smooth 1).continuous continuous_const)
  have hsub : {c : radialCircleBase | radialCircleDefining 0 c < 0 ∧
      radialCircleDefining 1 c < 0} ⊆ radialCircleBundle.cbase := by
    intro c hc
    apply radial_cbase_iff.mpr
    intro l
    fin_cases l
    · exact hc.1.le
    · exact hc.2.le
  have hi := interior_maximal hsub ho ⟨hs0, hs1⟩
  exact (hb.2 hi).elim

def radialOtherFace (l : Fin 2) : Fin 2 := if l = 0 then 1 else 0

theorem radialOtherFace_ne (l : Fin 2) : radialOtherFace l ≠ l := by
  fin_cases l <;> decide

def radialFaceNeighbourhood (l : Fin 2) : TopologicalSpace.Opens radialCircleBase :=
  ⟨{b | radialCircleDefining (radialOtherFace l) b < 0},
    isOpen_lt (radialCircleDefining_smooth _).continuous continuous_const⟩

theorem radial_active_neighbourhood (b : radialCircleBase) (l : Fin 2)
    (hb : b ∈ radialCircleBundle.cbase) (hl : radialCircleDefining l b = 0) :
    b ∈ radialFaceNeighbourhood l := by
  have hle := radial_cbase_iff.mp hb (radialOtherFace l)
  rcases hle.eq_or_lt with h | h
  · exact (radialCircleDefining_no_double b (radialOtherFace_ne l) h hl).elim
  · exact h

theorem radial_local_cbase (l : Fin 2) :
    radialCircleBundle.cbase ∩ (radialFaceNeighbourhood l : Set radialCircleBase) =
      {b | b ∈ radialFaceNeighbourhood l ∧ radialCircleDefining l b ≤ 0} := by
  ext b
  constructor
  · intro hb
    exact ⟨hb.2, radial_cbase_iff.mp hb.1 l⟩
  · rintro ⟨hn, hl⟩
    refine ⟨radial_cbase_iff.mpr ?_, hn⟩
    intro j
    by_cases hj : j = l
    · subst j
      exact hl
    · have he : j = radialOtherFace l := by
        fin_cases l <;> fin_cases j <;> simp_all [radialOtherFace]
      rw [he]
      exact hn.le

theorem radial_defining_onto (l : Fin 2) (b : radialCircleBase) :
    Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (radialCircleDefining l) b) := by
  let d : TangentSpace (𝓡 2) b →L[ℝ] ℝ :=
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (radialCircleDefining l) b
  change Surjective d
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp (radialCircleDefining_regular l b)
  have hn : d v ≠ 0 := by
    change d v ≠ 0 at hv
    exact hv
  intro r
  refine ⟨(r / d v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn]

theorem radial_local_faces : ∀ c ∈ frontier radialCircleBundle.cbase,
    ∃ U : TopologicalSpace.Opens radialCircleBase, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel radialSlims.ResidualFace
          radialEdgeBundle.EdgeBaseComponent))
        (φ : CircleFaceLabel radialSlims.ResidualFace radialEdgeBundle.EdgeBaseComponent →
          radialCircleBase → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ radialCircleBundle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ radialCircleBundle.cbase ∧
              radialCircleBundle.fibre c' ⊆ circleFaceSet radialSlims radialEdgeBundle f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        radialCircleBundle.cbase ∩ (U : Set radialCircleBase) =
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  classical
  intro c hc
  obtain ⟨l, hl⟩ := radial_frontier_active c hc
  have hm : c ∈ radialCircleBundle.cbase :=
    radialCircleCornerBase_compact.isClosed.frontier_subset hc
  let L : Finset (CircleFaceLabel radialSlims.ResidualFace
      radialEdgeBundle.EdgeBaseComponent) := {radialFaceEquiv l}
  let φ : CircleFaceLabel radialSlims.ResidualFace radialEdgeBundle.EdgeBaseComponent →
      radialCircleBase → ℝ := fun f => radialCircleDefining (radialFaceEquiv.symm f)
  have hφ : φ (radialFaceEquiv l) = radialCircleDefining l := by
    change radialCircleDefining (radialFaceEquiv.symm (radialFaceEquiv l)) = _
    rw [radialFaceEquiv.symm_apply_apply]
  refine ⟨radialFaceNeighbourhood l, radial_active_neighbourhood c l hm hl,
    L, φ, ?_, ?_, ?_, ?_, ?_⟩
  · simp [L]
  · simp [L]
  · intro f hf
    have he : f = radialFaceEquiv l := Finset.mem_singleton.mp hf
    subst f
    rw [hφ]
    refine ⟨(radialCircleDefining_smooth l).contMDiffOn, hl, ?_⟩
    ext b
    simp only [mem_ofPred_eq]
    rw [radial_fibre_face_iff]
  · intro g
    let k : L := ⟨radialFaceEquiv l, Finset.mem_singleton_self _⟩
    obtain ⟨w, hw⟩ := radial_defining_onto l c (g k)
    refine ⟨w, ?_⟩
    funext f
    have he : f = k := Subtype.ext (Finset.mem_singleton.mp f.property)
    rw [he]
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ (radialFaceEquiv l)) c w = g k
    rw [hφ]
    exact hw
  · rw [radial_local_cbase]
    ext b
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hn, hb⟩
      refine ⟨hn, ?_⟩
      intro f hf
      have he : f = radialFaceEquiv l := Finset.mem_singleton.mp hf
      rw [he, hφ]
      exact hb
    · rintro ⟨hn, hb⟩
      refine ⟨hn, ?_⟩
      have h := hb (radialFaceEquiv l) (Finset.mem_singleton_self _)
      rwa [hφ] at h

end GC.GraphManifold.Assembly.FC39P0.X135Radial
