import DifferentialGeometry.Topology.Attachment.SourceChartGluing
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.IntrinsicOverlap

section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology ENNReal

universe u uE uH

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

namespace IntrinsicBallChart

variable {ι : Type uE} (g : SmoothRiemannianMetric I M)
  (hEnorm : ∀ (x : M) (v : TangentSpace I x),
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
  (x : ι → M) {ρ : Real} (hρ : 0 < ρ)
  (c : ∀ i, IntrinsicBallChart (I := I) g hEnorm (x i) ρ)
  (near : ι → ι → Bool)
  (hnear : ∀ i j,
    (near i j = true → edist (x i) (x j) < ENNReal.ofReal (ρ / 4)) ∧
    (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i) (x j)))

include hρ hnear in
omit [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace M] in
private theorem near_refl (i : ι) : near i i = true := by
  by_contra hi
  have hbad := (hnear i i).2 (Bool.eq_false_iff.mpr hi)
  simp only [edist_self] at hbad
  exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < ρ / 4)).not_ge hbad

include hnear in
omit [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M] [CompleteSpace M] in
private theorem near_symm (i j : ι) (hij : near i j = true) : near j i = true := by
  by_contra hji
  have hbad := (hnear j i).2 (Bool.eq_false_iff.mpr hji)
  rw [edist_comm] at hbad
  exact (hnear i j).1 hij |>.not_ge hbad

include hρ in
private theorem core_subset_source (i : ι) :
    Metric.ball (0 : E) (ρ / 10) ⊆ (c i).hom.toOpenPartialHomeomorph.source := by
  change Metric.ball (0 : E) (ρ / 10) ⊆ (c i).hom.source
  rw [(c i).source_eq]
  exact Metric.ball_subset_ball (by linarith)

include hρ hnear in
private theorem core_images_disjoint (i j : ι) (hij : near i j = false) :
    Disjoint ((c i).hom.toOpenPartialHomeomorph '' Metric.ball (0 : E) (ρ / 10))
      ((c j).hom.toOpenPartialHomeomorph '' Metric.ball (0 : E) (ρ / 10)) := by
  apply (c i).disjoint_image_ball_of_add_le_edist g hEnorm (x i) (x j) (c j)
    (by linarith) (by linarith)
  calc
    ENNReal.ofReal (ρ / 10) + ENNReal.ofReal (ρ / 10) = ENNReal.ofReal (ρ / 10 + ρ / 10) :=
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (ρ / 4) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ edist (x i) (x j) := (hnear i j).2 hij

include hρ hnear in
private theorem core_mapsTo_target (i j : ι) (hij : near i j = true) :
    MapsTo (c i).hom.toOpenPartialHomeomorph (Metric.ball (0 : E) (ρ / 10))
      (c j).hom.toOpenPartialHomeomorph.target := by
  have hmargin : edist (x i) (x j) + ENNReal.ofReal (ρ / 10) ≤ ENNReal.ofReal ρ := by
    calc
      edist (x i) (x j) + ENNReal.ofReal (ρ / 10) ≤
          ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 10) :=
        add_le_add_left ((hnear i j).1 hij).le _
      _ = ENNReal.ofReal (ρ / 4 + ρ / 10) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
  have hov := (c i).overlap_on_ball_of_edist_add_le g hEnorm (x i) (x j) (c j)
    hρ hρ (by linarith : ρ / 10 ≤ ρ) hmargin
  intro z hz
  obtain ⟨w, hw, hzw⟩ := (hov z hz).2
  change (c i).hom z ∈ (c j).hom.target
  change (c j).hom w = (c i).hom z at hzw
  change w ∈ Metric.ball (0 : E) ρ at hw
  rw [← hzw]
  exact (c j).hom.map_source (by rw [(c j).source_eq]; exact hw)

def coreGluing : TopCat.GlueData.{uE} :=
  TopCat.GlueData.ofOpenPartialHomeomorphs
    (fun i => (c i).hom.toOpenPartialHomeomorph) (Metric.ball (0 : E) (ρ / 10))
    Metric.isOpen_ball (core_subset_source g hEnorm x hρ c) near
    (near_refl x hρ near hnear) (near_symm x near hnear)
    (core_images_disjoint g hEnorm x hρ c near hnear)
    (core_mapsTo_target g hEnorm x hρ c near hnear)

def coreHomeomorphUnion :
    (coreGluing g hEnorm x hρ c near hnear).toGlueData.glued ≃ₜ
      (⋃ i, (c i).hom '' Metric.ball (0 : E) (ρ / 10) : Set M) :=
  TopCat.GlueData.homeomorphUnionImage
    (fun i => (c i).hom.toOpenPartialHomeomorph) (Metric.ball (0 : E) (ρ / 10))
    Metric.isOpen_ball (core_subset_source g hEnorm x hρ c) near
    (near_refl x hρ near hnear) (near_symm x near hnear)
    (core_images_disjoint g hEnorm x hρ c near hnear)
    (core_mapsTo_target g hEnorm x hρ c near hnear)

@[simp]
theorem coreHomeomorphUnion_ι (i : ι) (z : Metric.ball (0 : E) (ρ / 10)) :
    ↑(coreHomeomorphUnion g hEnorm x hρ c near hnear
      ((coreGluing g hEnorm x hρ c near hnear).toGlueData.ι i z)) = (c i).hom z := by
  exact TopCat.GlueData.homeomorphUnionImage_ι
    (fun i => (c i).hom.toOpenPartialHomeomorph) (Metric.ball (0 : E) (ρ / 10))
    Metric.isOpen_ball (core_subset_source g hEnorm x hρ c) near
    (near_refl x hρ near hnear) (near_symm x near hnear)
    (core_images_disjoint g hEnorm x hρ c near hnear)
    (core_mapsTo_target g hEnorm x hρ c near hnear) i z

theorem coreHomeomorphUnion_ι_zero (i : ι) :
    ↑(coreHomeomorphUnion g hEnorm x hρ c near hnear
      ((coreGluing g hEnorm x hρ c near hnear).toGlueData.ι i
        ⟨0, Metric.mem_ball_self (by positivity : 0 < ρ / 10)⟩)) = x i := by
  rw [coreHomeomorphUnion_ι]
  exact ((c i).toNormalBallChart g hEnorm (x i) hρ).map_zero

@[simp]
theorem coreHomeomorphUnion_symm_apply (i : ι) (z : Metric.ball (0 : E) (ρ / 10)) :
    (coreHomeomorphUnion g hEnorm x hρ c near hnear).symm
      ⟨(c i).hom z, mem_iUnion.mpr ⟨i, ⟨z, z.property, rfl⟩⟩⟩ =
      (coreGluing g hEnorm x hρ c near hnear).toGlueData.ι i z := by
  apply (coreHomeomorphUnion g hEnorm x hρ c near hnear).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (coreHomeomorphUnion_ι g hEnorm x hρ c near hnear i z).symm

end IntrinsicBallChart

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
