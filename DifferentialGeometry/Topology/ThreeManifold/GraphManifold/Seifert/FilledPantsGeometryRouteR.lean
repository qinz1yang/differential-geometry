import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryAssembly

/-!
# Route R for the one-cone family, against the standard-carrier input

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §0
route R, with review 21 §3). For charts `C` of a block whose data have `ports = 2` and
`cones = [(p, q)]`, route R (`Seifert/FilledPantsGeometryNormalise.lean`) identifies the data with
`oneConeData p q` (`eq_oneConeData`), moves the cone to hole `1` by a hole relabelling (the
relabelled charts keep the matrix, not the literal seam models: `exists_pantsReindexedCharts`
proves the compatibility equation and shrinks the tubes), rebases to the standard Bézout pair
`(-gcdB p q, gcdA p q)` (`exists_oneConeNormalisedCharts`) and compares interiors with the
standard carrier (`compareInterior`). Here the standard-carrier geometry is the explicit input
`hone` (lane A4D2's `oneConeBlock_interiorGeometry` once delivered), an existence statement with
its model equation; `oneConeGeometryOfCharts` transports the chosen geometry and its model is
`.hyperbolicProduct` by the transport lemma (`rfl`) followed by `Classical.choose_spec`, not by
`rfl`. `oneConeGeometryOfData` reads `p` and `q` off `d.cones`, for use in the final case split.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

section Standard

variable (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1)

def oneConeGeometryOfCharts (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)])
    (hone : ∀ (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1),
      ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct) :
    W.InteriorGeometry ⊤ :=
  oneConeInteriorGeometryOfCharts p q hp hpq C hports hcones (Classical.choose (hone p q hp hpq))

theorem oneConeGeometryOfCharts_model (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)])
    (hone : ∀ (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1),
      ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (oneConeGeometryOfCharts p q hp hpq C hports hcones hone).model =
      ThurstonModel.hyperbolicProduct :=
  (oneConeInteriorGeometryOfCharts_model p q hp hpq C hports hcones _).trans
    (Classical.choose_spec (hone p q hp hpq))

end Standard

def SeifertData.firstConeOrder (d : SeifertData) : ℕ := (d.cones.headD (0, 0)).1

def SeifertData.firstConeTwist (d : SeifertData) : ℤ := (d.cones.headD (0, 0)).2

theorem SeifertData.cones_eq_firstCone (h : ∃ p : ℕ, ∃ q : ℤ, d.cones = [(p, q)]) :
    d.cones = [(d.firstConeOrder, d.firstConeTwist)] := by
  obtain ⟨p, q, hpq⟩ := h
  simp [SeifertData.firstConeOrder, SeifertData.firstConeTwist, hpq]

def oneConeGeometryOfData (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcone : ∃ p : ℕ, ∃ q : ℤ, d.cones = [(p, q)])
    (hone : ∀ (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1),
      ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct) :
    W.InteriorGeometry ⊤ :=
  oneConeGeometryOfCharts d.firstConeOrder d.firstConeTwist
    (SeifertData.two_le_of_oneCone (SeifertData.cones_eq_firstCone hcone))
    (SeifertData.gcd_of_oneCone (SeifertData.cones_eq_firstCone hcone)) C hports
    (SeifertData.cones_eq_firstCone hcone) hone

theorem oneConeGeometryOfData_model (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcone : ∃ p : ℕ, ∃ q : ℤ, d.cones = [(p, q)])
    (hone : ∀ (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1),
      ∃ G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤,
        letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
          (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
        G.model = ThurstonModel.hyperbolicProduct) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (oneConeGeometryOfData C hports hcone hone).model = ThurstonModel.hyperbolicProduct :=
  oneConeGeometryOfCharts_model _ _ _ _ C hports _ hone

end GC.Seifert
