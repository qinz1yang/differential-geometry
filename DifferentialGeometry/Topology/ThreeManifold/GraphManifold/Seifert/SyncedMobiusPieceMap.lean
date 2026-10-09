import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SyncedMobiusPieceRestrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SyncedMobiusPieceChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SyncedMobiusPieceModel

/-!
# The Möbius circle bundle onto the preimage of an embedded Möbius piece

Lane MD5b, step (2) of `exists_syncedMobiusPiece`. A `PieceData F M` bundles the data of the
frozen hypothesis `hMD5`: a Möbius base `M` smoothly embedded by `ι` in the interior of the base of
`F`, with a bicollar `c` of its boundary circle. Over `K = range ι` the fibration restricts
(`total`, `fib`, base identified with `M.surface` by `baseDiffeo`), and the twisted chart of the
restriction with smooth local left inverses (`circleBundlesOverPlanarBases_mobius_localInv`) gives
`Ψ : (S¹ × I) × S¹ → U`, two-to-one along `mobiusDeck`. The model chart of
`mobiusBundleSet` (`MobiusModelChart.chart`) has the same identifications, so
`χ₀ = Ψ ∘ chart⁻¹` is well defined (`modelSection` is any section of `chart`); locally it is `Ψ`
composed with a smooth local section, hence smooth with bijective differential, and it is an
injective map onto `π⁻¹ K` taking exactly the boundary torus to `π⁻¹ (c (S¹ × 0))`
(`mem_zero_iff`). Its inverse `χinv` is smooth along smooth maps into `π⁻¹ K`
(`contMDiffOn_χinv`): near a point it is the model chart composed with a local left inverse of `Ψ`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace MobiusPiece

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

def modelSection : mobiusBundleSet.{u} → (Circle × unitInterval) × Circle :=
  surjInv MobiusModelChart.surjective_chart

theorem chart_modelSection (x : mobiusBundleSet.{u}) :
    MobiusModelChart.chart (modelSection x) = x :=
  surjInv_eq MobiusModelChart.surjective_chart x

structure PieceData (F : CircleFibration C U) (M : MobiusBase.{u}) where
  ι : M.surface.Carrier → F.base.Carrier
  hι : Manifold.IsSmoothEmbedding (SurfaceModel.model M.surface.kind)
    (SurfaceModel.model F.base.kind) ∞ ι
  c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind) (Circle × ℝ)
    F.base.Carrier ∞
  hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}
  b : Bool
  σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle
  hcol : ∀ t s (hs : 0 ≤ s), s < 1 → ι (M.collar (t, halfPoint s hs)) = c (σ t, if b then s else -s)
  hint : ∀ q, (SurfaceModel.model F.base.kind).IsInteriorPoint (ι q)

namespace PieceData

variable {F : CircleFibration C U} {M : MobiusBase.{u}} (D : PieceData F M)

def atlas : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range D.ι) :=
  Classical.choice (nonempty_mobiusAtlas M D.hι D.c D.hc D.b D.σ D.hcol D.hint)

theorem isClosed_range : IsClosed (range D.ι) :=
  (isCompact_range D.hι.contMDiff.continuous).isClosed

abbrev total : CompactCarrier.{u} := CircleFibration.restrictTotal F D.atlas D.isClosed_range

abbrev fib : CircleFibration D.total ⊤ :=
  letI := connectedSpace_range_mobius F M D.hι
  CircleFibration.restrict F D.atlas D.isClosed_range

def baseDiffeo : D.fib.base.Carrier ≃ₘ⟮SurfaceModel.model D.fib.base.kind,
    SurfaceModel.model M.surface.kind⟯ M.surface.Carrier :=
  letI := connectedSpace_range_mobius F M D.hι
  (mobiusDiffeo F M D.hι D.atlas D.isClosed_range).symm

theorem exists_chart :
    ∃ Ψ : (Circle × unitInterval) × Circle → (⊤ : TopologicalSpace.Opens D.total.Carrier),
      IsTwistedChart D.fib (M.embedding ∘ D.baseDiffeo) Ψ ∧
      ∀ p₀, ∃ W : Set D.total.Carrier, IsOpen W ∧ (Ψ p₀ : D.total.Carrier) ∈ W ∧
        ∃ G : D.total.Carrier → (Circle × unitInterval) × Circle,
          ContMDiffOn D.total.model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ G W ∧
          ∀ᶠ p in 𝓝 p₀, G (Ψ p : D.total.Carrier) = p :=
  circleBundlesOverPlanarBases_mobius_localInv D.total ⊤ D.fib M D.baseDiffeo

def chartF : (Circle × unitInterval) × Circle → (⊤ : TopologicalSpace.Opens D.total.Carrier) :=
  Classical.choose D.exists_chart

def Ψ (p : (Circle × unitInterval) × Circle) : U := (D.chartF p).val.val

def χ₀ (x : mobiusBundleSet.{u}) : U := D.Ψ (modelSection x)

def χinv (y : U) : mobiusBundleSet.{u} := invFun D.χ₀ y

theorem spec_chart : IsTwistedChart D.fib (M.embedding ∘ D.baseDiffeo) D.chartF ∧
    ∀ p₀, ∃ W : Set D.total.Carrier, IsOpen W ∧ (D.chartF p₀ : D.total.Carrier) ∈ W ∧
      ∃ G : D.total.Carrier → (Circle × unitInterval) × Circle,
        ContMDiffOn D.total.model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ G W ∧
        ∀ᶠ p in 𝓝 p₀, G (D.chartF p : D.total.Carrier) = p :=
  Classical.choose_spec D.exists_chart

theorem contMDiff_Ψ : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model ∞
    (fun p => (D.Ψ p).val) :=
  contMDiff_subtype_val.comp ((CircleFibration.contMDiff_restrictTotal_val F D.atlas
    D.isClosed_range).comp (contMDiff_subtype_val.comp D.spec_chart.1.1))

theorem Ψ_eq_Ψ_iff (p q : (Circle × unitInterval) × Circle) :
    D.Ψ p = D.Ψ q ↔ q = p ∨ q = mobiusDeck p := by
  rw [← D.spec_chart.1.2.2.1 p q]
  constructor
  · intro h
    exact Subtype.ext (Subtype.ext h)
  · intro h
    change (D.chartF p).val.val = (D.chartF q).val.val
    rw [h]

theorem Ψ_modelSection_chart (p : (Circle × unitInterval) × Circle) :
    D.Ψ (modelSection (MobiusModelChart.chart p)) = D.Ψ p :=
  ((D.Ψ_eq_Ψ_iff p _).mpr ((MobiusModelChart.chart_eq_chart_iff p _).mp
    (chart_modelSection _).symm)).symm

theorem χ₀_eq_of_chart {s : mobiusBundleSet.{u} → (Circle × unitInterval) × Circle}
    {x : mobiusBundleSet.{u}} (hx : MobiusModelChart.chart (s x) = x) : D.χ₀ x = D.Ψ (s x) := by
  change D.Ψ (modelSection x) = _
  conv_lhs => rw [← hx]
  exact D.Ψ_modelSection_chart (s x)

theorem contMDiff_χ₀ : ContMDiff (𝓡∂ 3) C.model ∞ (fun x => (D.χ₀ x).val) := by
  intro x₀
  obtain ⟨V, hV, hx₀, s, hs, hchart⟩ := MobiusModelChart.exists_localSection x₀
  have h := D.contMDiff_Ψ.contMDiffAt.comp x₀ (hs.contMDiffAt (hV.mem_nhds hx₀))
  apply h.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hx₀] with x hx
  change (D.χ₀ x).val = (D.Ψ (s x)).val
  rw [D.χ₀_eq_of_chart (hchart x hx)]

theorem injective_χ₀ : Injective D.χ₀ := by
  intro x y h
  have h1 := (D.Ψ_eq_Ψ_iff _ _).mp h
  have h2 := (MobiusModelChart.chart_eq_chart_iff _ _).mpr h1
  rw [chart_modelSection, chart_modelSection] at h2
  exact h2

theorem injective_mfderiv_Ψ (p : (Circle × unitInterval) × Circle) :
    Injective (mfderiv (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model (fun p => (D.Ψ p).val) p) := by
  let T := D.total
  let y := D.chartF p
  have hΨd : MDifferentiableAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) T.model D.chartF p :=
    D.spec_chart.1.1.mdifferentiableAt (by simp)
  have hv1 : MDifferentiableAt T.model T.model
      (Subtype.val : (⊤ : TopologicalSpace.Opens T.Carrier) → T.Carrier) y :=
    (contMDiff_subtype_val (I := T.model) (n := ∞)).mdifferentiableAt (by simp)
  have hv2 : MDifferentiableAt T.model C.model (fun z : T.Carrier => (z.val : U)) y.val :=
    (CircleFibration.contMDiff_restrictTotal_val F D.atlas D.isClosed_range).mdifferentiableAt
      (by simp)
  have hv3 : MDifferentiableAt C.model C.model (Subtype.val : U → C.Carrier) y.val.val :=
    (contMDiff_subtype_val (I := C.model) (n := ∞)).mdifferentiableAt (by simp)
  have H := hv3.hasMFDerivAt.comp p (hv2.hasMFDerivAt.comp p (hv1.hasMFDerivAt.comp p
    hΨd.hasMFDerivAt))
  have hc : mfderiv (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model (fun p => (D.Ψ p).val) p =
      (mfderiv C.model C.model (Subtype.val : U → C.Carrier) y.val.val).comp
        ((mfderiv T.model C.model (fun z : T.Carrier => (z.val : U)) y.val).comp
          ((mfderiv T.model T.model
            (Subtype.val : (⊤ : TopologicalSpace.Opens T.Carrier) → T.Carrier) y).comp
            (mfderiv (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) T.model D.chartF p))) :=
    H.mfderiv
  rw [hc]
  have b1 : Injective (mfderiv C.model C.model (Subtype.val : U → C.Carrier) y.val.val) := by
    rw [mfderiv_subtype_val (I := C.model) U y.val.val]
    exact injective_id
  have b2 : Injective (mfderiv T.model C.model (fun z : T.Carrier => (z.val : U)) y.val) :=
    ((CircleFibration.totalAtlas F D.atlas).mfderiv_subtypeVal_bijective y.val).1
  have b3 : Injective (mfderiv T.model T.model
      (Subtype.val : (⊤ : TopologicalSpace.Opens T.Carrier) → T.Carrier) y) := by
    rw [mfderiv_subtype_val (I := T.model) ⊤ y]
    exact injective_id
  exact b1.comp (b2.comp (b3.comp (D.spec_chart.1.2.2.2.1 p)))

theorem bijective_mfderiv_χ₀ (x : mobiusBundleSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) C.model (fun x => (D.χ₀ x).val) x) := by
  obtain ⟨V, hV, hx, s, hs, hchart⟩ := MobiusModelChart.exists_localSection x
  have hsd : MDifferentiableAt (𝓡∂ 3) (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) s x :=
    (hs.contMDiffAt (hV.mem_nhds hx)).mdifferentiableAt (by simp)
  have hΨd : MDifferentiableAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) C.model
      (fun p => (D.Ψ p).val) (s x) := D.contMDiff_Ψ.mdifferentiableAt (by simp)
  have hev : (fun x => (D.χ₀ x).val) =ᶠ[𝓝 x] (fun p => (D.Ψ p).val) ∘ s := by
    filter_upwards [hV.mem_nhds hx] with y hy
    change (D.χ₀ y).val = (D.Ψ (s y)).val
    rw [D.χ₀_eq_of_chart (hchart y hy)]
  have hsinj : Injective (mfderiv (𝓡∂ 3) (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) s x) := by
    refine MobiusCover.injective_mfderiv_of_leftInverse hsd
      (MobiusModelChart.contMDiff_chart.mdifferentiableAt (by simp)) ?_
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hchart y hy
  have hinj : Injective (mfderiv (𝓡∂ 3) C.model (fun x => (D.χ₀ x).val) x) := by
    rw [hev.mfderiv_eq, mfderiv_comp x hΨd hsd]
    exact (D.injective_mfderiv_Ψ (s x)).comp hsinj
  let _ : FiniteDimensional ℝ (TangentSpace (𝓡∂ 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  let _ : FiniteDimensional ℝ (TangentSpace C.model (D.χ₀ x).val) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡∂ 3) x) =
      Module.finrank ℝ (TangentSpace C.model (D.χ₀ x).val) := rfl
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (mfderiv (𝓡∂ 3) C.model (fun x => (D.χ₀ x).val) x).toLinearMap)).mp hinj⟩

theorem range_Ψ : range D.Ψ = F.projection ⁻¹' range D.ι := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact (D.chartF p).val.2
  · intro hy
    obtain ⟨p, hp⟩ := D.spec_chart.1.2.1 ⟨⟨y, hy⟩, trivial⟩
    refine ⟨p, ?_⟩
    change (D.chartF p).val.val = y
    rw [hp]

theorem range_χ₀ : range D.χ₀ = F.projection ⁻¹' range D.ι := by
  rw [← D.range_Ψ]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨MobiusModelChart.chart p, D.Ψ_modelSection_chart p⟩

theorem exists_mobiusPoint_zero_iff (z : Circle) (t : unitInterval) :
    (∃ z' : Circle, mobiusPoint z t = mobiusPoint z' 0) ↔ ((t : ℝ) = 0 ∨ (t : ℝ) = 1) := by
  constructor
  · rintro ⟨z', h⟩
    rw [MobiusCover.mobiusPoint_eq_modelOf, MobiusCover.mobiusPoint_eq_modelOf] at h
    have ht := t.2
    have habs : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have habs' : |2 * ((0 : unitInterval) : ℝ) - 1| ≤ 1 := by norm_num
    rcases MobiusCover.eq_of_modelOf_eq (Circle.norm_coe z) (Circle.norm_coe z') habs habs' h with
      ⟨-, h2⟩ | ⟨-, h2⟩
    · left
      simp only [Set.Icc.coe_zero] at h2
      linarith
    · right
      simp only [Set.Icc.coe_zero] at h2
      linarith
  · rintro (h | h)
    · refine ⟨z, ?_⟩
      have : t = 0 := Subtype.ext h
      rw [this]
    · refine ⟨-z, ?_⟩
      rw [MobiusCover.mobiusPoint_eq_modelOf, MobiusCover.mobiusPoint_eq_modelOf, h,
        Circle.coe_neg, ← MobiusCover.modelOf_neg]
      norm_num

theorem ι_baseDiffeo (k : D.fib.base.Carrier) : D.ι (D.baseDiffeo k) = k.val := by
  let _ := connectedSpace_range_mobius F M D.hι
  have h2 := (mobiusDiffeo F M D.hι D.atlas D.isClosed_range).toEquiv.apply_symm_apply k
  exact (mobiusDiffeo_apply_val F M D.hι D.atlas D.isClosed_range _).symm.trans
    (congrArg Subtype.val h2)

theorem projection_Ψ (p : (Circle × unitInterval) × Circle) :
    F.projection (D.Ψ p) = D.ι (D.baseDiffeo (D.fib.projection (D.chartF p))) := by
  rw [D.ι_baseDiffeo]
  rfl

theorem mem_zero_iff (x : mobiusBundleSet.{u}) :
    F.projection (D.χ₀ x) ∈ range (fun θ : Circle => D.c (θ, 0)) ↔ (𝓡∂ 3).IsBoundaryPoint x := by
  set p := modelSection x
  set q := D.baseDiffeo (D.fib.projection (D.chartF p))
  have hq : M.embedding q = mobiusPoint p.1.1 p.1.2 := D.spec_chart.1.2.2.2.2 p
  change F.projection (D.Ψ p) ∈ _ ↔ _
  rw [D.projection_Ψ p, mem_zero_mobius_iff M D.hι D.c D.b D.σ D.hcol q]
  conv_rhs => rw [← chart_modelSection x, MobiusModelChart.isBoundaryPoint_chart_iff]
  rw [← exists_mobiusPoint_zero_iff p.1.1 p.1.2]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [← hq, ← ht, M.embedding_collar]⟩
  · rintro ⟨z', hz'⟩
    refine ⟨z', M.isSmoothEmbedding.isEmbedding.injective ?_⟩
    rw [M.embedding_collar, hq, hz']

theorem χinv_χ₀ (x : mobiusBundleSet.{u}) : D.χinv (D.χ₀ x) = x :=
  leftInverse_invFun D.injective_χ₀ x

theorem χ₀_χinv {y : U} (hy : y ∈ range D.χ₀) : D.χ₀ (D.χinv y) = y :=
  invFun_eq hy

theorem isClosedEmbedding_χ₀ : Topology.IsClosedEmbedding D.χ₀ := by
  have _ : CompactSpace mobiusBundleSet.{u} := mobiusBundleCarrier.{u}.compact
  have hc : Continuous D.χ₀ := by
    have h := D.contMDiff_χ₀.continuous
    exact continuous_induced_rng.mpr h
  exact hc.isClosedEmbedding D.injective_χ₀

def liftT (y : U) : D.total.Carrier := (D.chartF (modelSection (D.χinv y))).val

theorem liftT_val {y : U} (hy : y ∈ range D.χ₀) : (D.liftT y).val = y :=
  D.χ₀_χinv hy

theorem contMDiffOn_χinv {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] {HX : Type*}
    [TopologicalSpace HX] {J : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X]
    [ChartedSpace HX X] {g : X → U} {V : Set X} (hV : IsOpen V)
    (hg : ContMDiffOn J C.model ∞ (fun x => (g x).val) V) (hgr : ∀ x ∈ V, g x ∈ range D.χ₀) :
    ContMDiffOn J (𝓡∂ 3) ∞ (fun x => D.χinv (g x)) V := by
  intro x₀ hx₀
  set n₀ := D.χinv (g x₀)
  obtain ⟨VN, hVN, hn₀, s, hs, hchart⟩ := MobiusModelChart.exists_localSection n₀
  obtain ⟨W, hW, hq₀W, G, hG, hGev⟩ := D.spec_chart.2 (s n₀)
  have hgU : ContMDiffAt J C.model ∞ g x₀ :=
    (ContMDiffAt.subtypeVal_comp_iff U g x₀).mp (hg.contMDiffAt (hV.mem_nhds hx₀))
  have hlift : ContMDiffAt J D.total.model ∞ (fun x => D.liftT (g x)) x₀ := by
    have h1 : ContMDiffAt J C.model ∞ (fun x => (g x).val) x₀ :=
      hg.contMDiffAt (hV.mem_nhds hx₀)
    have h2 : ContMDiffAt J C.model ∞ (fun x => ((D.liftT (g x)).val).val) x₀ := by
      apply h1.congr_of_eventuallyEq
      filter_upwards [hV.mem_nhds hx₀] with x hx
      rw [D.liftT_val (hgr x hx)]
    have h3 : ContMDiffAt J C.model ∞ (fun x => (D.liftT (g x)).val) x₀ :=
      (ContMDiffAt.subtypeVal_comp_iff U _ x₀).mp h2
    exact contMDiffWithinAt_univ.mp
      (((CircleFibration.totalAtlas F D.atlas).contMDiffWithinAt_iff_subtype_val
        (fun x => D.liftT (g x)) univ x₀).mpr h3.contMDiffWithinAt)
  have hten : Tendsto (fun x => D.χinv (g x)) (𝓝 x₀) (𝓝 n₀) := by
    rw [D.isClosedEmbedding_χ₀.isInducing.tendsto_nhds_iff]
    have hgc : Tendsto g (𝓝 x₀) (𝓝 (g x₀)) := hgU.continuousAt
    rw [D.χ₀_χinv (hgr x₀ hx₀)]
    apply hgc.congr'
    filter_upwards [hV.mem_nhds hx₀] with x hx
    exact (D.χ₀_χinv (hgr x hx)).symm
  have hsc : ContinuousAt s n₀ := (hs.contMDiffAt (hVN.mem_nhds hn₀)).continuousAt
  have hev1 : ∀ᶠ x in 𝓝 x₀, D.χinv (g x) ∈ VN := hten (hVN.mem_nhds hn₀)
  have hev2 : ∀ᶠ x in 𝓝 x₀, G (D.chartF (s (D.χinv (g x))) : D.total.Carrier) =
      s (D.χinv (g x)) := (hsc.tendsto.comp hten) hGev
  have hkey : ∀ x ∈ V, D.χinv (g x) ∈ VN →
      (D.chartF (s (D.χinv (g x))) : D.total.Carrier) = D.liftT (g x) := by
    intro x hx hxN
    apply Subtype.ext
    rw [D.liftT_val (hgr x hx)]
    change D.Ψ (s (D.χinv (g x))) = g x
    rw [← D.χ₀_eq_of_chart (hchart _ hxN), D.χ₀_χinv (hgr x hx)]
  have hev3 : (fun x => D.χinv (g x)) =ᶠ[𝓝 x₀]
      (fun x => MobiusModelChart.chart (G (D.liftT (g x)))) := by
    filter_upwards [hev1, hev2, hV.mem_nhds hx₀] with x h1 h2 h3
    rw [← hkey x h3 h1, h2, hchart _ h1]
  have hW' : D.liftT (g x₀) ∈ W := by
    rw [← hkey x₀ hx₀ hn₀]
    exact hq₀W
  have hsm : ContMDiffAt J (𝓡∂ 3) ∞ (fun x => MobiusModelChart.chart (G (D.liftT (g x)))) x₀ :=
    MobiusModelChart.contMDiff_chart.contMDiffAt.comp x₀
      ((hG.contMDiffAt (hW.mem_nhds hW')).comp x₀ hlift)
  exact (hsm.congr_of_eventuallyEq hev3).contMDiffWithinAt

end PieceData

end MobiusPiece

end GC.Seifert
