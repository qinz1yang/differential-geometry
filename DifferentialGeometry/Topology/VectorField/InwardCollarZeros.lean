import DifferentialGeometry.Topology.VectorField.InwardCollarOutwardization

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  {J : ModelWithCorners ℝ E H} {ε δ a : ℝ} [Fact ((0 : ℝ) < ε)]
  (S : Opens (B × Icc (0 : ℝ) ε))
  (hS : (S : Set (B × Icc (0 : ℝ) ε)) = {q | q.2.val < δ})
  (T : ∀ p : B, TangentSpace J p) (b : B → ℝ)
  (G : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q)
  (hboundary : ∀ p, T p = 0 → b p ≠ 0)
  (hzero : ∀ q : S, G q = 0 ↔ q.val.2.val ≤ a ∧
    collarExtension T b collarTransition (q.val.1, 1 - q.val.2.val / a) = 0)
  (ha : 0 < a)

include hS hboundary hzero ha

omit hS in
theorem inwardCollar_zero_height {q : S} (hq : G q = 0) :
    q.val.2.val ∈ Ioo (a / 3) (2 * a / 3) := by
  have hh := collarExtension_zero_height_mem_Ioo (hboundary q.val.1) ((hzero q).mp hq).2
  change 1 / 3 < 1 - q.val.2.val / a ∧ 1 - q.val.2.val / a < 2 / 3 at hh
  have hlo : (1 / 3) * a < q.val.2.val := (lt_div_iff₀ ha).mp (by linarith : 1 / 3 < q.val.2.val / a)
  have hhi : q.val.2.val < (2 / 3) * a := (div_lt_iff₀ ha).mp (by linarith : q.val.2.val / a < 2 / 3)
  constructor <;> linarith


theorem inwardCollar_zeroSet_proj_bijOn (haδ : a < δ) (haε : a ≤ ε) :
    BijOn (fun q : S => q.val.1) {q | G q = 0} {p | T p = 0 ∧ b p < 0} := by
  have hbij := collarExtension_zeroSet_proj_bijOn hboundary
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact hbij.mapsTo ((hzero q).mp hq).2
  · intro q hq r hr he
    have hp := hbij.injOn ((hzero q).mp hq).2 ((hzero r).mp hr).2 he
    have ht : 1 - q.val.2.val / a = 1 - r.val.2.val / a := congrArg Prod.snd hp
    apply Subtype.ext
    apply Prod.ext he
    apply Subtype.ext
    exact (div_left_inj' ha.ne').mp (by linarith)
  · intro p hp
    obtain ⟨t, ht, _⟩ := existsUnique_collarExtension_eq_zero hp.1 hp.2
    have htime := collarExtension_zero_height_mem_Ioo (hboundary p) ht
    change 1 / 3 < t ∧ t < 2 / 3 at htime
    let r := a * (1 - t)
    have hr0 : 0 ≤ r := mul_nonneg ha.le (by linarith)
    have hra : r ≤ a := by dsimp [r]; nlinarith
    let q : S := ⟨(p, ⟨r, hr0, hra.trans haε⟩), (Set.ext_iff.mp hS _).mpr (hra.trans_lt haδ)⟩
    refine ⟨q, (hzero q).mpr ⟨hra, ?_⟩, rfl⟩
    have he : 1 - q.val.2.val / a = t := by change 1 - a * (1 - t) / a = t; field_simp; ring
    change collarExtension T b collarTransition (p, 1 - q.val.2.val / a) = 0
    rw [he]
    exact ht


theorem finite_inwardCollar_zeroSet (haδ : a < δ) (haε : a ≤ ε)
    (hfinite : {p | T p = 0}.Finite) : {q | G q = 0}.Finite :=
  (inwardCollar_zeroSet_proj_bijOn S hS T b G hboundary hzero ha haδ haε).finite_iff_finite.mpr
    (hfinite.subset (fun _ h => h.1))

end DifferentialGeometry.VectorField
