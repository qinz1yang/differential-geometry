import DifferentialGeometry.Tensor.BilinearForm.HalfSpaceExtension
import DifferentialGeometry.Tensor.BilinearForm.Smoothness
import DifferentialGeometry.Geometry.Metric.LocalRealization

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Tensor
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric

section OpenSet
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_local_metric_on
    (b : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (O : TopologicalSpace.Opens M)
    (hb : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (b y)) O)
    (hsymm : ∀ y ∈ O, ∀ v w : TangentSpace I y, b y v w = b y w v)
    (q : M) (hq : q ∈ O)
    (hpos : ∀ v : TangentSpace I q, v ≠ 0 → 0 < b q v v) :
    ∃ U : TopologicalSpace.Opens M, q ∈ U ∧ U ≤ O ∧
      ∃ g : SmoothRiemannianMetric I U,
        ∀ (y : U) (v w : TangentSpace I y), g.inner y v w = b (y : M) v w := by
  let bO : ∀ y : O, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    fun y => b (y : M)
  obtain ⟨V, hqV, gV, hgV⟩ := exists_local_metric_of_bilinear_section bO
    (contMDiff_bilinear_restrictOpen b O hb) (fun y v w => hsymm y y.2 v w)
    ⟨q, hq⟩ hpos
  let U : TopologicalSpace.Opens M :=
    ⟨Subtype.val '' (V : Set O), O.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ V.isOpen⟩
  have hqU : q ∈ U := ⟨⟨q, hq⟩, hqV, rfl⟩
  have hUO : U ≤ O := by
    rintro y ⟨z, hz, rfl⟩
    exact z.2
  have hposU : ∀ y ∈ U, ∀ v : TangentSpace I y, v ≠ 0 → 0 < b y v v := by
    rintro y ⟨z, hz, rfl⟩ v hv
    have hp := gV.pos ⟨z, hz⟩ v hv
    have heq : gV.inner ⟨z, hz⟩ v v = b (z : M) v v := hgV ⟨z, hz⟩ v v
    exact heq ▸ hp
  refine ⟨U, hqU, hUO, ?_⟩
  refine ⟨{
    inner := fun y : U => b (y : M)
    symm := fun y v w => hsymm (y : M) (hUO y.2) v w
    pos := fun y v hv => hposU (y : M) y.2 v hv
    isVonNBounded := fun y => posDef_isVonNBounded (E := E) (b (y : M)) (hposU (y : M) y.2)
    contMDiff := contMDiff_bilinear_restrictOpen b U (hb.mono hUO) }, ?_⟩
  intro y v w
  rfl
end OpenSet

section Cylinder
variable {E H S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S] [T2Space S]

theorem exists_local_metric_extension_of_halfClosed_cylinder_section
    (b : ∀ y : S × ℝ, TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ] ℝ)
    {A : ℝ}
    (hb : ContMDiffOn (I.prod 𝓘(ℝ))
      ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun y : S × ℝ => TotalSpace.mk' ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) y (b y))
      (univ ×ˢ Ioc (-A) 0))
    (hsymm : ∀ y ∈ (univ ×ˢ Ioc (-A) 0 : Set (S × ℝ)),
      ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y, b y v w = b y w v)
    (hpos : ∀ y ∈ (univ ×ˢ Ioc (-A) 0 : Set (S × ℝ)),
      ∀ v : TangentSpace (I.prod 𝓘(ℝ)) y, v ≠ 0 → 0 < b y v v)
    (q : S × ℝ) (hq : q ∈ univ ×ˢ Ioc (-A) 0) :
    ∃ U : TopologicalSpace.Opens (S × ℝ), q ∈ U ∧
      (U : Set (S × ℝ)) ⊆ univ ×ˢ Ioi (-A) ∧
      ∃ g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U,
        ∀ y : U, (y : S × ℝ) ∈ univ ×ˢ Ioc (-A) 0 →
          ∀ v w : TangentSpace (I.prod 𝓘(ℝ)) y,
            g.inner y v w = b (y : S × ℝ) v w := by
  let : ∀ y : S × ℝ, ContinuousAdd (TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ] ℝ) :=
    fun y => inferInstance
  by_cases hq0 : q.2 = 0
  · have hA : 0 < A := by linarith [hq.2.1, hq.2.2]
    obtain ⟨O, hqO, hOleft, B, hB, hBeq⟩ :=
      exists_contMDiffOn_bilinear_extension_across_cylinder_boundary b hA hb q hq0
    let C : ∀ y : S × ℝ, TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ]
        TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ] ℝ :=
      fun y => (fun C : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ =>
        (1 / 2 : ℝ) • (C + C.flip)) (B y)
    have hC : ContMDiffOn (I.prod 𝓘(ℝ))
        ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
        (fun y : S × ℝ => TotalSpace.mk' ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) y (C y)) O :=
      contMDiffOn_bilinear_symmetrize hB
    have hCval (y : S × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) y) :
        C y v w = (1 / 2 : ℝ) * (B y v w + B y w v) := rfl
    have hCsymm (y : S × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) y) :
        C y v w = C y w v := by
      rw [hCval, hCval]
      ring
    have hCeq : ∀ y ∈ (O : Set (S × ℝ)) ∩ (univ ×ˢ Ioc (-A) 0), C y = b y := by
      intro y hy
      ext v w
      rw [hCval, hBeq y hy, hsymm y hy.2 v w]
      ring
    have hCpos : ∀ v : TangentSpace (I.prod 𝓘(ℝ)) q, v ≠ 0 → 0 < C q v v := by
      rw [hCeq q ⟨hqO, hq⟩]
      exact hpos q hq
    obtain ⟨U, hqU, hUO, g, hg⟩ := exists_local_metric_on C O hC
      (fun y _ v w => hCsymm y v w) q hqO hCpos
    refine ⟨U, hqU, fun y hy => hOleft (hUO hy), g, ?_⟩
    intro y hy v w
    rw [hg, hCeq (y : S × ℝ) ⟨hUO y.2, hy⟩]
  · have hqneg : q.2 < 0 := lt_of_le_of_ne hq.2.2 hq0
    let O : TopologicalSpace.Opens (S × ℝ) :=
      ⟨univ ×ˢ Ioo (-A) 0, isOpen_univ.prod isOpen_Ioo⟩
    have hqO : q ∈ O := ⟨mem_univ _, hq.2.1, hqneg⟩
    have hOD : (O : Set (S × ℝ)) ⊆ univ ×ˢ Ioc (-A) 0 :=
      prod_mono_right Ioo_subset_Ioc_self
    obtain ⟨U, hqU, hUO, g, hg⟩ := exists_local_metric_on b O (hb.mono hOD)
      (fun y hy v w => hsymm y (hOD hy) v w) q hqO (hpos q hq)
    refine ⟨U, hqU, fun y hy => ⟨mem_univ _, (hUO hy).2.1⟩, g, ?_⟩
    intro y _ v w
    exact hg y v w
end Cylinder
end DifferentialGeometry.Geometry.Metric
