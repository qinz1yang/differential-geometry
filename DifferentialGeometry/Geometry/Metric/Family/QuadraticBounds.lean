import DifferentialGeometry.Geometry.Metric.Family.Basic

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_tensor_quadratic_bound_on_compact
    [T2Space M]
    (g : ℝ → SmoothRiemannianMetric I M)
    (A : (t : ℝ) → (x : M) → Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x)
    {J : Set ℝ} (hJ : IsCompact J) {K : Set M} (hK : IsCompact K)
    (hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (g t) x))
    (hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ J, ∀ x ∈ K, ∀ v : TangentSpace I x,
      |quad02 (I := I) (M := M) (A t x) v| ≤ C * (g t).inner x v v := by
  let U := MetricUnitTangent (I := I) (M := M) (g 0)
  let S : Set U := {p | MetricUnitTangent.base (I := I) (M := M) p ∈ K}
  have hS : IsCompact S := metricUnitOn_compact (I := I) (g 0) hK
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  let f : J × U → ℝ := fun p => |quad02 (I := I) (M := M) (A p.1.1 p.2.1.proj) p.2.1.2|
  let q : J × U → ℝ := fun p => (g p.1.1).inner p.2.1.proj p.2.1.2 p.2.1.2
  have hpull : Continuous (fun p : J × U => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hf : Continuous f := by
    exact ((tensor0SFamily_quadCont (I := I) (M := M) hA).comp hpull).abs
  have hq : Continuous q := by
    have hcont := (tensor0SFamily_quadCont (I := I) (M := M) hg).comp hpull
    simpa only [q, quad02, Tensor0SBundle.metricTensorField_apply, Function.comp_def] using hcont
  have hqpos (p : J × U) : 0 < q p := by
    apply (g p.1.1).pos
    intro hv
    have hunit := p.2.2
    rw [hv] at hunit
    simp at hunit
  have hratio : Continuous (fun p : J × U => f p / q p) :=
    hf.div hq (fun p => (hqpos p).ne')
  have hsource : IsCompact ((univ : Set J) ×ˢ S) := isCompact_univ.prod hS
  obtain ⟨B, hB⟩ := hsource.bddAbove_image hratio.continuousOn
  let C : ℝ := max B 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro t ht x hx v
  by_cases hv : v = 0
  · subst v
    have hzero : quad02 (I := I) (M := M) (A t x) (0 : TangentSpace I x) = 0 := by
      with_unfolding_all exact (A t x).map_coord_zero (0 : Fin 2) rfl
    simp only [hzero, abs_zero, map_zero, mul_zero, le_refl]
  have hvpos : 0 < (g 0).inner x v v := (g 0).pos x v hv
  let s : ℝ := Real.sqrt ((g 0).inner x v v)
  have hspos : 0 < s := Real.sqrt_pos.mpr hvpos
  have hsne : s ≠ 0 := hspos.ne'
  have hss : s * s = (g 0).inner x v v := by
    simpa only [s, sq] using Real.sq_sqrt hvpos.le
  have hunit : (g 0).inner x (s⁻¹ • v) (s⁻¹ • v) = 1 := by
    rw [metric_smul2]
    field_simp [hsne]
    linarith [hss]
  let p : U := ⟨(⟨x, s⁻¹ • v⟩ : TangentBundle I M), hunit⟩
  let z : J × U := (⟨t, ht⟩, p)
  have hz : z ∈ (univ : Set J) ×ˢ S := ⟨mem_univ _, hx⟩
  have hratioBound : f z / q z ≤ C :=
    (hB (mem_image_of_mem (fun z => f z / q z) hz)).trans (le_max_left _ _)
  have hbound := (div_le_iff₀ (hqpos z)).1 hratioBound
  have hfz : f z = (s⁻¹ * s⁻¹) * |quad02 (I := I) (M := M) (A t x) v| := by
    dsimp [f, z, p]
    rw [tensor02_smul2, abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  have hqz : q z = s⁻¹ * s⁻¹ * (g t).inner x v v := metric_smul2 (g t) s⁻¹ v
  rw [hfz, hqz] at hbound
  have hm := mul_le_mul_of_nonneg_right hbound (mul_self_nonneg s)
  have hleft : (s⁻¹ * s⁻¹ * |quad02 (I := I) (M := M) (A t x) v|) * (s * s) =
      |quad02 (I := I) (M := M) (A t x) v| := by field_simp
  have hright : (C * (s⁻¹ * s⁻¹ * (g t).inner x v v)) * (s * s) =
      C * (g t).inner x v v := by field_simp
  rwa [hleft, hright] at hm

end DifferentialGeometry.Geometry.Curvature
