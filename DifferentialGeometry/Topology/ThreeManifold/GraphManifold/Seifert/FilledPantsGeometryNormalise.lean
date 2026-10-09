import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanTwisted

/-!
# Route R: a one-cone block is interior-diffeomorphic to the standard filled carrier

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §0
route R). For Seifert data of the one-cone family (`ports = 2`, `cones = [(p, q)]`) the data equal
`oneConeData p q` (`eq_oneConeData`). Given charts `C` of such a block, the hole relabelling
`exists_pantsReindexedCharts` moves the cone to hole `1`, i.e. to the port equivalence `portEquiv`
of the standard carrier (`exists_oneConePortCharts`); two Bézout pairs for the same slope differ by
a multiple of `(p, q)`, so one `rebasis` makes the matrices equal to those of `filledCharts`
(`exists_oneConeNormalisedCharts`); `compareInterior` then identifies the interior of the block with
the interior of `(coneFillingOf p q).filledCarrier` (`exists_oneConeInteriorDiffeomorph`). Any
interior geometry of the standard carrier transports to the block with the same model
(`oneConeInteriorGeometryOfCharts`, `_model` by `rfl`). The standard carrier is wrapped in the
definition `oneConeStandardCarrier` (equal to `filledCarrier` by `rfl`) so that the interior
instances of `CompactCarrier` are found syntactically in model statements.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem SeifertData.oneCone_counts (p : ℕ) (q : ℤ) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)]) : d.k = 3 ∧ d.normals = [] ∧ d.fillingCount = 1 := by
  have h := d.ports_add_length_add_length
  rw [hports, hcones] at h
  simp only [List.length_cons, List.length_nil] at h
  have hn : d.normals.length = 0 := by have hk := d.k_le_three; omega
  have he : d.normals = [] := List.length_eq_zero_iff.mp hn
  refine ⟨by omega, he, ?_⟩
  simp [SeifertData.fillingCount, hcones, he]

theorem SeifertData.two_le_of_oneCone {p : ℕ} {q : ℤ} (hcones : d.cones = [(p, q)]) : 2 ≤ p :=
  d.two_le_of_mem_cones (p, q) (by simp [hcones])

theorem SeifertData.gcd_of_oneCone {p : ℕ} {q : ℤ} (hcones : d.cones = [(p, q)]) :
    Int.gcd (p : ℤ) q = 1 :=
  d.gcd_eq_one_of_mem_cones (p, q) (by simp [hcones])

theorem SeifertData.eq_oneConeData {p : ℕ} {q : ℤ} (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)]) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1) :
    d = oneConeData p q hp hpq := by
  obtain ⟨hk, hn, _⟩ := SeifertData.oneCone_counts p q hports hcones
  cases d
  dsimp only at hports hcones hk hn
  subst_vars
  rfl

section Standard

variable (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1)

theorem exists_oneConePortCharts (C : SeifertBlockCharts W (oneConeData p q hp hpq)) :
    ∃ D : SeifertBlockCharts W (oneConeData p q hp hpq),
      D.port = (coneFillingOf p q hp hpq).portEquiv hp ∧ D.matrix = C.matrix := by
  let ρ : Fin 3 ≃ Fin 3 := C.port.symm.trans ((coneFillingOf p q hp hpq).portEquiv hp)
  obtain ⟨D, hD, hmatrix⟩ := C.exists_pantsReindexedCharts rfl ρ
  refine ⟨D, hD.trans ?_, hmatrix⟩
  apply Equiv.ext
  intro x
  change (coneFillingOf p q hp hpq).portEquiv hp (C.port.symm (C.port x)) = _
  rw [C.port.symm_apply_apply]

theorem exists_oneConeNormalisedCharts (C : SeifertBlockCharts W (oneConeData p q hp hpq)) :
    ∃ D : SeifertBlockCharts W (oneConeData p q hp hpq),
      D.port = ((coneFillingOf p q hp hpq).filledCharts.{u} hp).port ∧
        ∀ m, D.matrix m = ((coneFillingOf p q hp hpq).filledCharts.{u} hp).matrix m := by
  obtain ⟨D, hport, -⟩ := exists_oneConePortCharts p q hp hpq C
  set c := coneFillingOf p q hp hpq with hc
  have hslope : ∀ m, (oneConeData p q hp hpq).fillingSlope m = ((p : ℤ), q) :=
    c.fillingSlope_oneConeData hp
  have hcop : IsCoprime (p : ℤ) q := Int.isCoprime_iff_gcd_eq_one.mpr hpq
  have hdvd : ∀ m, ∃ n : ℤ, D.a m - c.a = (p : ℤ) * n := by
    intro m
    have h1 := D.bezout m
    rw [hslope m] at h1
    have h2 : (p : ℤ) * c.b - c.a * q = 1 := c.det_eq
    have hmul : (p : ℤ) ∣ q * (D.a m - c.a) :=
      ⟨D.b m - c.b, by linear_combination h2 - h1⟩
    exact hcop.dvd_of_dvd_mul_left hmul
  choose n hn using hdvd
  refine ⟨D.rebasis n, hport, fun m => ?_⟩
  have h1 := D.bezout m
  rw [hslope m] at h1
  have h2 : (p : ℤ) * c.b - c.a * q = 1 := c.det_eq
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have ha : (D.rebasis n).a m = c.a := by
    change D.a m - ((oneConeData p q hp hpq).fillingSlope m).1 * n m = c.a
    rw [hslope m]
    linarith [hn m]
  have hb : (D.rebasis n).b m = c.b := by
    change D.b m - ((oneConeData p q hp hpq).fillingSlope m).2 * n m = c.b
    rw [hslope m]
    apply mul_left_cancel₀ hp0
    linear_combination h1 - h2 + q * hn m
  apply Units.ext
  rw [(D.rebasis n).matrix_eq m, (c.filledCharts.{u} hp).matrix_eq m, ha, hb]
  rfl

def oneConeStandardCarrier : CompactCarrier.{u} := (coneFillingOf p q hp hpq).filledCarrier

theorem oneConeStandardCarrier_eq :
    oneConeStandardCarrier.{u} p q hp hpq = (coneFillingOf p q hp hpq).filledCarrier := rfl

theorem exists_oneConeInteriorDiffeomorph (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)]) :
    Nonempty (W.pieceInterior ⊤ ≃ₘ⟮W.model, (oneConeStandardCarrier.{u} p q hp hpq).model⟯
      (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤) := by
  have hd := SeifertData.eq_oneConeData hports hcones hp hpq
  subst hd
  obtain ⟨D, hport, hmatrix⟩ := exists_oneConeNormalisedCharts p q hp hpq C
  exact ⟨D.compareInterior ((coneFillingOf p q hp hpq).filledCharts.{u} hp) hport hmatrix⟩

def oneConeInteriorDiffeomorph (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)]) :
    W.pieceInterior ⊤ ≃ₘ⟮W.model, (oneConeStandardCarrier.{u} p q hp hpq).model⟯
      (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤ :=
  Classical.choice (exists_oneConeInteriorDiffeomorph p q hp hpq C hports hcones)

def oneConeInteriorGeometryOfCharts (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)])
    (G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤) :
    W.InteriorGeometry ⊤ :=
  transportInteriorGeometry (oneConeInteriorDiffeomorph p q hp hpq C hports hcones) G

theorem oneConeInteriorGeometryOfCharts_model (C : SeifertBlockCharts W d) (hports : d.ports = 2)
    (hcones : d.cones = [(p, q)])
    (G : (oneConeStandardCarrier.{u} p q hp hpq).InteriorGeometry ⊤) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorChartedSpace (oneConeStandardCarrier.{u} p q hp hpq).model ∞
      (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
    letI := Manifold.interiorIsManifold (oneConeStandardCarrier.{u} p q hp hpq).model ∞
      (M := (oneConeStandardCarrier.{u} p q hp hpq).pieceInterior ⊤)
    (oneConeInteriorGeometryOfCharts p q hp hpq C hports hcones G).model = G.model :=
  rfl

end Standard

end GC.Seifert
