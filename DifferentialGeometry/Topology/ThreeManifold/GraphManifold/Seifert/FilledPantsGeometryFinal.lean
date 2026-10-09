import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryTwoCone
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryOneCone
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryRouteR
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeFoldData

/-!
# The geometry of every filled pants block

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §0 and
§6 tier T4, with review 21). For the two-cone data `twoConeData p₁ q₁ p₂ q₂` the charts are
relabelled so that the port is the outer circle and the cones sit at `3/2` and `-3/2`
(`exists_twoConePortCharts`); with the shape `θᵢ = π/pᵢ` and lane A4b3's fold
`twoConeFoldData`, route D (`twoConeGeometryOfFold`) gives an `H² × ℝ` interior geometry
(`standardTwoConeGeometry`). Transporting the charts along `d = twoConeData …` gives the two-cone
family for every block (`twoConeBlock_interiorGeometry`), which is the remaining input of
`filledPantsBlockGeometry_of_twoCone`; hence `filledPantsBlockGeometry` holds unconditionally.
`filledInteriorGeometryOfCharts` is the chart-level geometry of DA5 §0, by route R for one cone
and route D for two cones.
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

section Standard

variable (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ) (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂)
  (g₁ : Int.gcd (p₁ : ℤ) q₁ = 1) (g₂ : Int.gcd (p₂ : ℤ) q₂ = 1)

def twoConeFirst : Fin (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingCount :=
  ⟨0, show 0 < 2 by norm_num⟩

def twoConeSecond : Fin (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingCount :=
  ⟨1, show 1 < 2 by norm_num⟩

theorem fillingSlope_twoConeFirst :
    (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingSlope (twoConeFirst p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂) =
      ((p₁ : ℤ), q₁) :=
  rfl

theorem fillingSlope_twoConeSecond :
    (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingSlope (twoConeSecond p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂) =
      ((p₂ : ℤ), q₂) :=
  rfl

theorem twoCone_eq_first_or_second (m : Fin (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingCount) :
    m = twoConeFirst p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ ∨ m = twoConeSecond p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ := by
  obtain ⟨n, hn⟩ := m
  have hn' : n < 2 := hn
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem twoCone_slope_pos (m : Fin (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingCount) :
    0 < ((twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingSlope m).1 := by
  rcases twoCone_eq_first_or_second p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ m with rfl | rfl
  · rw [fillingSlope_twoConeFirst]
    change (0 : ℤ) < p₁
    exact_mod_cast (by omega : 0 < p₁)
  · rw [fillingSlope_twoConeSecond]
    change (0 : ℤ) < p₂
    exact_mod_cast (by omega : 0 < p₂)

variable {W : CompactCarrier.{u}} (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂))
  (hport : C.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3))

include hport in
theorem twoCone_port_ne_zero (m : Fin (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂).fillingCount) :
    (C.port (.inr m)).val ≠ 0 := by
  rcases twoCone_eq_first_or_second p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ m with rfl | rfl <;> rw [hport]
  · change (1 : ℕ) ≠ 0
    norm_num
  · change (2 : ℕ) ≠ 0
    norm_num

include hport in
theorem twoCone_tubeCentre_first :
    C.tubeCentre (twoConeFirst p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂) = ((3 / 2 : ℝ) : ℂ) := by
  unfold SeifertBlockCharts.tubeCentre
  rw [hport]
  rfl

include hport in
theorem twoCone_tubeCentre_second :
    C.tubeCentre (twoConeSecond p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂) = ((-(3 / 2) : ℝ) : ℂ) := by
  unfold SeifertBlockCharts.tubeCentre
  rw [hport]
  rfl

end Standard

section Route

variable (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ) (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂)
  (g₁ : Int.gcd (p₁ : ℤ) q₁ = 1) (g₂ : Int.gcd (p₂ : ℤ) q₂ = 1) (hne : ¬(p₁ = 2 ∧ p₂ = 2))
  {W : CompactCarrier.{u}}

open TwoConeFold.Fold

theorem twoCone_angle_first (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)) :
    (TwoConeFold.shape p₁ p₂ h₁ h₂ hne).θ₁ * (chartNumbers C (twoConeFirst p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)
      (twoConeSecond p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)).p₁ = Real.pi := by
  change Real.pi / p₁ * (p₁ : ℝ) = Real.pi
  exact div_mul_cancel₀ _ (by exact_mod_cast (by omega : p₁ ≠ 0))

theorem twoCone_angle_second (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)) :
    (TwoConeFold.shape p₁ p₂ h₁ h₂ hne).θ₂ * (chartNumbers C (twoConeFirst p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)
      (twoConeSecond p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)).p₂ = Real.pi := by
  change Real.pi / p₂ * (p₂ : ℝ) = Real.pi
  exact div_mul_cancel₀ _ (by exact_mod_cast (by omega : p₂ ≠ 0))

def standardTwoConeGeometryOfPort (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂))
    (hport : C.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) : W.InteriorGeometry ⊤ :=
  twoConeGeometryOfFold C (twoConeFirst p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)
    (twoConeSecond p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂) rfl
    (twoCone_port_ne_zero p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ C hport)
    (twoCone_slope_pos p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)
    (ConeShape.twoConeFoldData (TwoConeFold.shape p₁ p₂ h₁ h₂ hne)
      (twoCone_angle_first p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne C)
      (twoCone_angle_second p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne C))
    (twoCone_angle_first p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne C)
    (twoCone_angle_second p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne C)
    (twoCone_tubeCentre_first p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ C hport)
    (twoCone_tubeCentre_second p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ C hport)
    (twoCone_eq_first_or_second p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)

theorem standardTwoConeGeometryOfPort_model
    (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂))
    (hport : C.port = (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (standardTwoConeGeometryOfPort p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne C hport).model =
      ThurstonModel.hyperbolicProduct :=
  rfl

def standardTwoConeGeometry (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)) :
    W.InteriorGeometry ⊤ :=
  standardTwoConeGeometryOfPort p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne
    (Classical.choose (exists_twoConePortCharts p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ C))
    (Classical.choose_spec (exists_twoConePortCharts p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ C)).1

theorem standardTwoConeGeometry_model
    (C : SeifertBlockCharts W (twoConeData p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (standardTwoConeGeometry p₁ q₁ p₂ q₂ h₁ h₂ g₁ g₂ hne C).model =
      ThurstonModel.hyperbolicProduct :=
  rfl

end Route

section Block

variable (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ) {W : CompactCarrier.{u}} {d : SeifertData}

def twoConeGeometryOfCharts (C : SeifertBlockCharts W d) (hports : d.ports = 1)
    (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) (hne : ¬(p₁ = 2 ∧ p₂ = 2)) :
    W.InteriorGeometry ⊤ :=
  standardTwoConeGeometry p₁ q₁ p₂ q₂ (SeifertData.two_le_of_twoCone p₁ q₁ p₂ q₂ hcones).1
    (SeifertData.two_le_of_twoCone p₁ q₁ p₂ q₂ hcones).2
    (SeifertData.gcd_of_twoCone p₁ q₁ p₂ q₂ hcones).1
    (SeifertData.gcd_of_twoCone p₁ q₁ p₂ q₂ hcones).2 hne
    (SeifertData.eq_twoConeData p₁ q₁ p₂ q₂ hports hcones _ _ _ _ ▸ C)

theorem twoConeGeometryOfCharts_model (C : SeifertBlockCharts W d) (hports : d.ports = 1)
    (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) (hne : ¬(p₁ = 2 ∧ p₂ = 2)) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (twoConeGeometryOfCharts p₁ q₁ p₂ q₂ C hports hcones hne).model =
      ThurstonModel.hyperbolicProduct :=
  rfl

end Block

theorem twoConeBlock_interiorGeometry (W : CompactCarrier.{u}) (d : SeifertData)
    (B : SeifertBlock W d) (p₁ : ℕ) (q₁ : ℤ) (p₂ : ℕ) (q₂ : ℤ) (hports : d.ports = 1)
    (hcones : d.cones = [(p₁, q₁), (p₂, q₂)]) (hne : ¬(p₁ = 2 ∧ p₂ = 2)) :
    ∃ G : W.InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct := by
  obtain ⟨C⟩ := B.exists_charts torusMappingClassLinear_holds
  exact ⟨twoConeGeometryOfCharts p₁ q₁ p₂ q₂ C hports hcones hne,
    twoConeGeometryOfCharts_model p₁ q₁ p₂ q₂ C hports hcones hne⟩

theorem filledPantsBlockGeometry : FilledPantsBlockGeometry.{u} :=
  filledPantsBlockGeometry_of_twoCone fun W d B p₁ q₁ p₂ q₂ hports hcones hne =>
    twoConeBlock_interiorGeometry W d B p₁ q₁ p₂ q₂ hports hcones hne

section Charts

variable {W : CompactCarrier.{u}} {d : SeifertData}

def SeifertData.secondConeOrder (d : SeifertData) : ℕ := (d.cones.getD 1 (0, 0)).1

def SeifertData.secondConeTwist (d : SeifertData) : ℤ := (d.cones.getD 1 (0, 0)).2

theorem SeifertData.oneCone_of_filledPants (hk : d.k = 3) (hport : 0 < d.ports)
    (hχ : d.orbChi < 0) (hfill : 0 < d.fillingCount) (h2 : d.ports = 2) :
    ∃ p : ℕ, ∃ q : ℤ, d.cones = [(p, q)] := by
  rcases d.filledPants_cases hk hport hχ hfill with ⟨-, p, q, hc, -⟩ | ⟨h1, -⟩
  · exact ⟨p, q, hc⟩
  · omega

theorem SeifertData.twoCone_of_filledPants (hk : d.k = 3) (hport : 0 < d.ports)
    (hχ : d.orbChi < 0) (hfill : 0 < d.fillingCount) (h2 : d.ports ≠ 2) :
    d.ports = 1 ∧ d.cones = [(d.firstConeOrder, d.firstConeTwist),
      (d.secondConeOrder, d.secondConeTwist)] ∧
      ¬(d.firstConeOrder = 2 ∧ d.secondConeOrder = 2) := by
  rcases d.filledPants_cases hk hport hχ hfill with ⟨h, -⟩ | ⟨h1, p₁, q₁, p₂, q₂, hc, -, hne⟩
  · exact absurd h h2
  · have hf : d.firstConeOrder = p₁ := by simp [SeifertData.firstConeOrder, hc]
    have hs : d.secondConeOrder = p₂ := by simp [SeifertData.secondConeOrder, hc]
    refine ⟨h1, ?_, by rw [hf, hs]; exact hne⟩
    simp [SeifertData.firstConeOrder, SeifertData.firstConeTwist, SeifertData.secondConeOrder,
      SeifertData.secondConeTwist, hc]

def filledInteriorGeometryOfCharts (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (hport : 0 < d.ports) (hχ : d.orbChi < 0) (hfill : 0 < d.fillingCount) :
    W.InteriorGeometry ⊤ :=
  if h2 : d.ports = 2 then
    oneConeGeometryOfData C h2 (SeifertData.oneCone_of_filledPants hk hport hχ hfill h2)
      fun p q hp hpq => oneConeBlock_interiorGeometry p q hp hpq
  else
    twoConeGeometryOfCharts d.firstConeOrder d.firstConeTwist d.secondConeOrder d.secondConeTwist C
      (SeifertData.twoCone_of_filledPants hk hport hχ hfill h2).1
      (SeifertData.twoCone_of_filledPants hk hport hχ hfill h2).2.1
      (SeifertData.twoCone_of_filledPants hk hport hχ hfill h2).2.2

theorem filledInteriorGeometryOfCharts_model (C : SeifertBlockCharts W d) (hk : d.k = 3)
    (hport : 0 < d.ports) (hχ : d.orbChi < 0) (hfill : 0 < d.fillingCount) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (filledInteriorGeometryOfCharts C hk hport hχ hfill).model =
      ThurstonModel.hyperbolicProduct := by
  unfold filledInteriorGeometryOfCharts
  split
  · exact oneConeGeometryOfData_model C _ _ _
  · exact twoConeGeometryOfCharts_model _ _ _ _ C _ _ _

end Charts

end GC.Seifert
