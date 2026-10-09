import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceReflection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Tensor

variable {E H S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]

theorem exists_contMDiffOn_bilinear_extension_across_cylinder_boundary
    (b : ∀ q : S × ℝ, TangentSpace (I.prod 𝓘(ℝ)) q →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ)) q →L[ℝ] ℝ)
    {A : ℝ} (hA : 0 < A)
    (hb : ContMDiffOn (I.prod 𝓘(ℝ))
      ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun q : S × ℝ => TotalSpace.mk' ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) q (b q))
      (univ ×ˢ Ioc (-A) 0))
    (q : S × ℝ) (hq : q.2 = 0) :
    ∃ U : TopologicalSpace.Opens (S × ℝ), q ∈ U ∧
      (U : Set (S × ℝ)) ⊆ univ ×ˢ Ioi (-A) ∧
      ∃ B : ∀ y : S × ℝ, TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ]
        TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ] ℝ,
        ContMDiffOn (I.prod 𝓘(ℝ))
          ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
          (fun y : S × ℝ => TotalSpace.mk' ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ) y (B y)) U ∧
        ∀ y ∈ (U : Set (S × ℝ)) ∩ (univ ×ˢ Ioc (-A) 0), B y = b y := by
  let : ∀ x : S × ℝ, ContinuousAdd (TangentSpace (I.prod 𝓘(ℝ)) x →L[ℝ] ℝ) :=
    fun x => inferInstance
  let F := (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ
  let V : S × ℝ → Type _ := fun y => TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ]
    TangentSpace (I.prod 𝓘(ℝ)) y →L[ℝ] ℝ
  let e := trivializationAt F V q
  let c := extChartAt I q.1
  let P : S × ℝ → E × ℝ := fun y => (c y.1, y.2)
  let K : E × ℝ → S × ℝ := fun y => (c.symm y.1, y.2)
  let O : Set (S × ℝ) := (c.source ×ˢ univ) ∩ e.baseSet ∩ (univ ×ˢ Ioi (-A))
  have hO : IsOpen O :=
    (((isOpen_extChartAt_source q.1).prod isOpen_univ).inter e.open_baseSet).inter
      (isOpen_univ.prod isOpen_Ioi)
  have hqO : q ∈ O := by
    refine ⟨⟨⟨mem_extChartAt_source q.1, mem_univ _⟩,
      mem_baseSet_trivializationAt F V q⟩, mem_univ _, ?_⟩
    rw [hq]
    exact neg_neg_of_pos hA
  have hP : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) ∞ P O := by
    apply (((contMDiffOn_extChartAt (I := I) (x := q.1)).comp contMDiffOn_fst
      (fun y hy => by
        change y.1 ∈ (chartAt H q.1).source
        simpa only [c, extChartAt_source] using hy.1.1.1)).prodMk_space contMDiffOn_snd)
  let W₀ : Set (E × ℝ) := c.target ×ˢ univ
  have hW₀ : IsOpen W₀ := (isOpen_extChartAt_target q.1).prod isOpen_univ
  have hK : ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod 𝓘(ℝ)) ∞ K W₀ :=
    (((contMDiffOn_extChartAt_symm (I := I) q.1).comp
      contDiff_fst.contMDiff.contMDiffOn (fun y hy => hy.1)).prodMk
      contDiff_snd.contMDiff.contMDiffOn)
  have hKP (y : S × ℝ) (hy : y ∈ O) : K (P y) = y := by
    apply Prod.ext
    · exact c.left_inv hy.1.1.1
    · rfl
  let W : Set (E × ℝ) := W₀ ∩ K ⁻¹' O
  have hW : IsOpen W := hK.continuousOn.isOpen_inter_preimage hW₀ hO
  have hqW : (c q.1, (0 : ℝ)) ∈ W := by
    have heq : (c q.1, (0 : ℝ)) = P q := by simp only [P, hq]
    rw [heq]
    exact ⟨⟨c.map_source (mem_extChartAt_source q.1), mem_univ _⟩,
      by change K (P q) ∈ O; rwa [hKP q hqO]⟩
  let f : E × ℝ → F := fun y => (e ⟨K y, b (K y)⟩).2
  have hcoeff : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞
      (fun y : S × ℝ => (e ⟨y, b y⟩).2) (O ∩ (univ ×ˢ Ioc (-A) 0)) := by
    have he : MapsTo (fun y : S × ℝ => (⟨y, b y⟩ : TotalSpace F V))
        (O ∩ (univ ×ˢ Ioc (-A) 0)) e.source := fun y hy => hy.1.1.2
    exact (e.contMDiffOn_iff he).mp (hb.mono inter_subset_right) |>.2
  have hf : ContDiffOn ℝ ∞ f (W ∩ (univ ×ˢ Iic (0 : ℝ))) := by
    rw [← contMDiffOn_iff_contDiffOn]
    refine hcoeff.comp (hK.mono (fun y hy => hy.1.1)) ?_
    intro y hy
    refine ⟨hy.1.2, mem_univ _, (hy.1.2).2.2, ?_⟩
    exact hy.2.2
  obtain ⟨G, hG, hpG, _hGW, g, hg, heq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_negative_halfSpace_boundary
      hW hqW hf
  let U : TopologicalSpace.Opens (S × ℝ) :=
    ⟨O ∩ P ⁻¹' G, hP.continuousOn.isOpen_inter_preimage hO hG⟩
  have hqU : q ∈ U := by
    refine ⟨hqO, ?_⟩
    change P q ∈ G
    simpa only [P, hq] using hpG
  let B : ∀ y : S × ℝ, V y := fun y => e.symm y (g (P y))
  have hcoordB (y : S × ℝ) (hy : y ∈ U) : (e ⟨y, B y⟩).2 = g (P y) := by
    dsimp only [B]
    exact congrArg Prod.snd (e.apply_mk_symm hy.1.1.2 (g (P y)))
  refine ⟨U, hqU, fun y hy => hy.1.2, B, ?_, ?_⟩
  · apply (e.contMDiffOn_iff (fun y hy => hy.1.1.2)).mpr
    refine ⟨contMDiffOn_id, ?_⟩
    exact (hg.contMDiffOn.comp (hP.mono inter_subset_left) (fun y hy => hy.2)).congr
      (fun y hy => hcoordB y hy)
  · intro y hy
    have heqy : g (P y) = (e ⟨y, b y⟩).2 := by
      rw [heq ⟨hy.1.2, mem_univ _, hy.2.2.2⟩]
      change (e ⟨K (P y), b (K (P y))⟩).2 = _
      rw [hKP y hy.1.1]
    change e.symm y (g (P y)) = b y
    rw [heqy]
    exact e.symm_apply_apply_mk hy.1.1.1.2 (b y)

end DifferentialGeometry.Geometry.Tensor
