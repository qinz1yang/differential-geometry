import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryShapes
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryNormalise
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBlockGeometry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusMappingClassProof

/-!
# Assembly of `FilledPantsBlockGeometry` from the two families

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §0,
§6 tier T4). The frozen interface quantifies over blocks with `k = 3`, a filling, a port and
`openModelOf = .hyperbolicProduct`; by `filledPants_cases` the data are the one-cone family or the
two-cone family. For the one-cone family route R (`Seifert/FilledPantsGeometryNormalise.lean`)
transports any interior geometry of the standard carrier `oneConeStandardCarrier p q`
(`exists_oneConeInteriorGeometry_of_standard`); charts exist for every block because
`TorusMappingClassLinear` is proved (`torusMappingClassLinear_holds`). The two-cone family is
reduced to an explicit datum `twoConeData` (`eq_twoConeData`) with the cones at the holes `1`
and `2` and the port at the outer circle (`exists_twoConePortCharts`).
`filledPantsBlockGeometry_of_families` assembles the frozen statement from a geometry on every
standard one-cone carrier (lane A4D) and a geometry on every two-cone block (route D, this lane's
remaining tiers); nothing is assumed beyond these two explicit inputs.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

section OneCone

variable (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1)

theorem exists_oneConeInteriorGeometry_of_standard (C : SeifertBlockCharts W d)
    (hports : d.ports = 2) (hcones : d.cones = [(p, q)])
    (hG : ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct) :
    ∃ G : W.InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct := by
  obtain ⟨G, hGm⟩ := hG
  exact ⟨oneConeInteriorGeometryOfCharts p q hp hpq C hports hcones G,
    (oneConeInteriorGeometryOfCharts_model p q hp hpq C hports hcones G).trans hGm⟩

theorem SeifertBlock.exists_oneConeInteriorGeometry_of_standard (B : SeifertBlock W d)
    (hports : d.ports = 2) (hcones : d.cones = [(p, q)])
    (hG : ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
        (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct) :
    ∃ G : W.InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct :=
  GC.Seifert.exists_oneConeInteriorGeometry_of_standard p q hp hpq
    (Classical.choice (B.exists_charts torusMappingClassLinear_holds)) hports hcones hG

end OneCone

section TwoCone

variable (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ)

def twoConeData (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂) (g₁ : Int.gcd (p₁ : ℤ) q₁ = 1)
    (g₂ : Int.gcd (p₂ : ℤ) q₂ = 1) : SeifertData where
  k := 3
  ports := 1
  cones := [(p₁, q₁), (p₂, q₂)]
  normals := []
  one_le_k := by norm_num
  k_le_three := le_rfl
  two_le_of_mem_cones x hx := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  gcd_eq_one_of_mem_cones x hx := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact g₁
    · exact g₂
  ports_add_length_add_length := rfl

theorem SeifertData.twoCone_counts (hports : d.ports = 1)
    (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) :
    d.k = 3 ∧ d.normals = [] ∧ d.fillingCount = 2 := by
  have h := d.ports_add_length_add_length
  rw [hports, hcones] at h
  simp only [List.length_cons, List.length_nil] at h
  have hn : d.normals.length = 0 := by have hk := d.k_le_three; omega
  have he : d.normals = [] := List.length_eq_zero_iff.mp hn
  refine ⟨by omega, he, ?_⟩
  simp [SeifertData.fillingCount, hcones, he]

theorem SeifertData.two_le_of_twoCone (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) :
    2 ≤ p₁ ∧ 2 ≤ p₂ :=
  ⟨d.two_le_of_mem_cones (p₁, q₁) (by simp [hcones]),
    d.two_le_of_mem_cones (p₂, q₂) (by simp [hcones])⟩

theorem SeifertData.gcd_of_twoCone (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) :
    Int.gcd (p₁ : ℤ) q₁ = 1 ∧ Int.gcd (p₂ : ℤ) q₂ = 1 :=
  ⟨d.gcd_eq_one_of_mem_cones (p₁, q₁) (by simp [hcones]),
    d.gcd_eq_one_of_mem_cones (p₂, q₂) (by simp [hcones])⟩

theorem SeifertData.eq_twoConeData (hports : d.ports = 1)
    (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂)
    (g₁ : Int.gcd (p₁ : ℤ) q₁ = 1) (g₂ : Int.gcd (p₂ : ℤ) q₂ = 1) :
    d = twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ := by
  obtain ⟨hk, hn, _⟩ := SeifertData.twoCone_counts p₁ q₁ p₂ q₂ hports hcones
  cases d
  dsimp only at hports hcones hk hn
  subst_vars
  rfl

theorem exists_twoConePortCharts (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂) (g₁ : Int.gcd (p₁ : ℤ) q₁ = 1)
    (g₂ : Int.gcd (p₂ : ℤ) q₂ = 1)
    (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)) :
    ∃ D : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂),
      D.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3) ∧ D.matrix = C.matrix := by
  let ρ : Fin 3 ≃ Fin 3 := C.port.symm.trans finSumFinEquiv
  obtain ⟨D, hD, hmatrix⟩ := C.exists_pantsReindexedCharts rfl ρ
  refine ⟨D, hD.trans ?_, hmatrix⟩
  apply Equiv.ext
  intro x
  change finSumFinEquiv (C.port.symm (C.port x)) = finSumFinEquiv x
  rw [C.port.symm_apply_apply]

end TwoCone

theorem filledPantsBlockGeometry_of_families
    (hone : ∀ (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1),
      ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct)
    (htwo : ∀ (W : CompactCarrier.{u}) (d : SeifertData) (_ : SeifertBlock W d)
      (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ), d.ports = 1 → d.cones = [(p₁, q₁), (p₂, q₂)] →
      ¬ (p₁ = 2 ∧ p₂ = 2) →
      ∃ G : W.InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
        letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct) :
    FilledPantsBlockGeometry.{u} := by
  intro W d B hk hfill hopen hgood _ hmodel
  have hχ : d.orbChi < 0 := (d.openModelOf_eq_hyperbolicProduct_iff hopen hgood).mp hmodel
  rcases d.filledPants_cases hk hopen hχ hfill with
    ⟨hports, p, q, hcones, -⟩ | ⟨hports, p₁, q₁, p₂, q₂, hcones, -, hne⟩
  · have hp := SeifertData.two_le_of_oneCone hcones
    have hpq := SeifertData.gcd_of_oneCone hcones
    exact B.exists_oneConeInteriorGeometry_of_standard p q hp hpq hports hcones (hone p q hp hpq)
  · exact htwo W d B p₁ q₁ p₂ q₂ hports hcones hne

end GC.Seifert
