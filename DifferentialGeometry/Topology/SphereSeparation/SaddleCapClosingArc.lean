import DifferentialGeometry.Topology.Embedding.LevelFamily
import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Embedding.Graph
import DifferentialGeometry.Topology.Homeomorph.LevelIsotopy
import DifferentialGeometry.Topology.Morse.RegularLevel.QuadraticCap
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk
import DifferentialGeometry.Topology.Diffeomorph.Fiberwise
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere
import DifferentialGeometry.Topology.PlanarJordan.SaddleCapSides
import DifferentialGeometry.Topology.PlanarJordan.SmoothArc
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Embedding.Lift

open Set Metric Manifold
open scoped ContDiff Manifold
noncomputable section

open DifferentialGeometry.Topology.Morse
  (saddleBandLevelCurve contDiffOn_saddleBandLevelCurve IsCriticalPointAt
    image_superlevel_component_level_eq_sphere_of_quadratic_cap
    eq_saddleBandLevelCurve_of_isIntegralCurveOn)
open DifferentialGeometry.Analysis.ODE (saddleBandVectorField)

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_circle_parametrization_image_sphere
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane) {r : ℝ} (hr : 0 < r) :
    ∃ γ : AddCircle (1 : ℝ) → Schoenflies.Plane,
      IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
      range γ = G '' sphere 0 r := by
  obtain ⟨γ, hγ, hγrange⟩ := exists_isSmoothEmbedding_addCircle_range_eq_sphere
    (E := Schoenflies.Plane) (by simp) 0 hr
  refine ⟨G ∘ γ, hγ.diffeomorph_comp G, ?_⟩
  rw [range_comp, hγrange]

private theorem isEmbedding_saddleBandLevelCurve_interval
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {s τ h : ℝ}
    (hs : 0 ≤ s) (hτ : 0 < τ) (hh : 0 < h) (hh1 : h < 1) (σ : ℝ) :
    Topology.IsEmbedding (fun t : unitInterval =>
      B (saddleBandLevelCurve s τ σ (-h + (2 * h) * (t : ℝ)))) := by
  have hmem (t : unitInterval) : -h + (2 * h) * (t : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [t.property.1, t.property.2]
  have hc : Continuous (fun t : unitInterval =>
      B (saddleBandLevelCurve s τ σ (-h + (2 * h) * (t : ℝ)))) :=
    B.continuous.comp ((contDiffOn_saddleBandLevelCurve hs hτ σ).continuousOn.comp_continuous
      (by fun_prop) hmem)
  apply (hc.isClosedEmbedding ?_).isEmbedding
  intro x y hxy
  have heq := congrArg Prod.fst (B.injective hxy)
  change -h + (2 * h) * (x : ℝ) = -h + (2 * h) * (y : ℝ) at heq
  apply Subtype.ext
  nlinarith

theorem exists_saddleBandLevelCurve_complementary_arc_lift
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    {e : M → Schoenflies.Plane × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, Schoenflies.Plane × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    (G : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    {s τ σ h r a : ℝ} (hs : 0 ≤ s) (hτ : 0 < τ) (hh : 0 < h) (hh1 : h < 1)
    (hr : 0 < r)
    (hselected : B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ⊆ G '' sphere 0 r)
    (hcircle : (fun y => (y, a)) '' (G '' sphere 0 r) ⊆ range e) :
    ∃ β : unitInterval → Schoenflies.Plane, ∃ η : unitInterval → M,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β ∧
      ContMDiff (𝓡∂ 1) I ∞ η ∧ Topology.IsEmbedding η ∧
      (∀ t, e (η t) = (β t, a)) ∧
      β 0 = B (saddleBandLevelCurve s τ σ (-h)) ∧
      β 1 = B (saddleBandLevelCurve s τ σ h) ∧
      B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∪ range β = G '' sphere 0 r ∧
      B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∩ range β =
        {B (saddleBandLevelCurve s τ σ (-h)), B (saddleBandLevelCurve s τ σ h)} := by
  let α : unitInterval → Schoenflies.Plane := fun t =>
    B (saddleBandLevelCurve s τ σ (-h + (2 * h) * (t : ℝ)))
  have hα : Topology.IsEmbedding α := isEmbedding_saddleBandLevelCurve_interval B hs hτ hh hh1 σ
  have hαrange : range α = B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) := by
    have hp : range (fun t : unitInterval => -h + (2 * h) * (t : ℝ)) = Icc (-h) h := by
      have heq : (fun t : unitInterval => -h + (2 * h) * (t : ℝ)) =
          Schoenflies.reparam (-h) h ∘ (Subtype.val : unitInterval → ℝ) := by
        funext t
        dsimp [Schoenflies.reparam]
        ring
      rw [heq, range_comp, Subtype.range_coe, Schoenflies.image_reparam_I,
        uIcc_of_le (by linarith : -h ≤ h)]
    change range ((B ∘ saddleBandLevelCurve s τ σ) ∘ _) = _
    rw [range_comp, hp, image_comp]
  have hα0 : α 0 = B (saddleBandLevelCurve s τ σ (-h)) := by simp [α]
  have hα1 : α 1 = B (saddleBandLevelCurve s τ σ h) := by
    change B (saddleBandLevelCurve s τ σ (-h + (2 * h) * 1)) = _
    congr 2
    ring
  obtain ⟨γ, hγ, hγrange⟩ := exists_circle_parametrization_image_sphere G hr
  obtain ⟨β, hβ, h0, h1, hunion, hinter⟩ :=
    DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc_of_isEmbedding
      hγ hα (by rw [hαrange, hγrange]; exact hselected)
  have hβcircle : range β ⊆ G '' sphere 0 r := by
    rw [← hγrange, ← hunion]
    exact subset_union_right
  have hβe : range (fun t => (β t, a)) ⊆ range e := by
    rintro _ ⟨t, rfl⟩
    exact hcircle ⟨β t, hβcircle (mem_range_self t), rfl⟩
  let η := he.lift (fun t => (β t, a)) hβe
  have hη : ContMDiff (𝓡∂ 1) I ∞ η :=
    he.contMDiff_lift (hβ.contMDiff.prodMk_space contMDiff_const) hβe
  have heq : ∀ t, e (η t) = (β t, a) := he.comp_lift hβe
  have hηemb : Topology.IsEmbedding η := by
    apply Topology.IsEmbedding.of_comp hη.continuous he.contMDiff.continuous
    have hh := (isEmbedding_prodMkLeft a).comp hβ.isEmbedding
    simpa only [Function.comp_def, heq] using hh
  refine ⟨β, η, hβ, hη, hηemb, heq, h0.trans hα0, h1.trans hα1, ?_, ?_⟩
  · simpa only [hαrange, hγrange] using hunion
  · simpa only [hαrange, hα0, hα1] using hinter

theorem contMDiff_and_isSmoothEmbedding_level_arc_transport
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H}
    {e : M → Schoenflies.Plane × ℝ}
    (he : IsSmoothEmbedding I 𝓘(ℝ, Schoenflies.Plane × ℝ) ∞ e)
    {β : unitInterval → Schoenflies.Plane} {η : unitInterval → M}
    (hβ : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β)
    (hη : ContMDiff (𝓡∂ 1) I ∞ η)
    (Φ : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2))
    (hΦi : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2))
    (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞)
    {N : Set M} (hN : IsOpen N) (hηN : range η ⊆ N)
    {ell d δ τ : ℝ} (hwindow : δ + |τ| < d)
    (hheight : ∀ t ∈ Icc (-d) d, ∀ x ∈ N, (e (Φ t x)).2 = (e x).2 + t)
    (hηeq : ∀ u, e (η u) = (β u, ell + τ))
    (A : ℝ → (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (hAe : ∀ t ∈ Icc (-d) d, ∀ x, A t (e x) = e (Φ t x)) :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) I ∞
      (fun q : ℝ × unitInterval => Φ (q.1 - τ) (η q.2)) ∧
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Schoenflies.Plane) ∞
      (fun q : ℝ × unitInterval => (e (Φ (q.1 - τ) (η q.2))).1) ∧
    (∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞
        (fun u => (e (Φ (t - τ) (η u))).1) ∧
      ∀ u, (e (Φ (t - τ) (η u))).2 = ell + t) ∧
    (∀ u, Φ (τ - τ) (η u) = η u ∧
      (e (Φ (τ - τ) (η u))).1 = β u) ∧
    IsCompact ((fun q : ℝ × unitInterval => e (Φ (q.1 - τ) (η q.2))) ''
      (Icc (-δ) δ ×ˢ univ)) ∧
    ∃ V : Set (Schoenflies.Plane × ℝ), IsOpen V ∧
      e '' ((fun q : ℝ × M => Φ q.1 q.2) ''
        (Ioo (-d) d ×ˢ (N ∩ {x | (e x).2 = ell + τ}))) = V ∩ range e ∧
      (fun q : ℝ × unitInterval => e (Φ (q.1 - τ) (η q.2))) ''
        (Icc (-δ) δ ×ˢ univ) ⊆ V := by
  have hfamily : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) I ∞
      (fun q : ℝ × unitInterval => Φ (q.1 - τ) (η q.2)) :=
    hΦ.comp ((contMDiff_fst.sub contMDiff_const).prodMk (hη.comp contMDiff_snd))
  have hspatial := he.contMDiff.comp hfamily
  have hplane : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Schoenflies.Plane) ∞
      (fun q : ℝ × unitInterval => (e (Φ (q.1 - τ) (η q.2))).1) :=
    contDiff_fst.contMDiff.comp hspatial
  have htime (t : ℝ) (ht : t ∈ Icc (-δ) δ) : t - τ ∈ Ioo (-d) d := by
    constructor <;> linarith [ht.1, ht.2, neg_abs_le τ, le_abs_self τ]
  have hh (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) :
      (e (Φ (t - τ) (η u))).2 = ell + t := by
    rw [hheight (t - τ) ⟨(htime t ht).1.le, (htime t ht).2.le⟩
      (η u) (hηN (mem_range_self u)), hηeq]
    ring
  refine ⟨hfamily, hplane, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, hh t ht⟩
    have hbase : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane × ℝ) ∞
        (fun u => (β u, ell + τ)) := hβ.graph contDiff_const
    have hshift : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane × ℝ) ∞
        (fun u => e (Φ (t - τ) (η u))) := by
      have h := hbase.diffeomorph_comp (A (t - τ))
      convert h using 1
      funext u
      change e (Φ (t - τ) (η u)) = A (t - τ) (β u, ell + τ)
      rw [← hηeq, hAe (t - τ) ⟨(htime t ht).1.le, (htime t ht).2.le⟩]
    exact hshift.fst_Icc_of_snd_eq_const (hh t ht)
  · intro u
    rw [sub_self, hΦ0]
    exact ⟨rfl, congrArg Prod.fst (hηeq u)⟩
  · exact (isCompact_Icc.prod isCompact_univ).image hspatial.continuous
  · have hΩ : IsOpen ((fun q : ℝ × M => Φ q.1 q.2) ''
        (Ioo (-d) d ×ˢ (N ∩ {x | (e x).2 = ell + τ}))) := by
      apply Homeomorph.isOpen_image_prod_level_of_height_translation
        (fun t => (Φ t).toHomeomorph) hΦi.continuous
        (continuous_snd.comp he.contMDiff.continuous) hN isOpen_Ioo
      intro t ht x hx
      exact hheight t ⟨ht.1.le, ht.2.le⟩ x hx
    obtain ⟨V, hV, hVe⟩ := he.isEmbedding.isInducing.image_eq_isOpen_inter_range hΩ
    refine ⟨V, hV, hVe, ?_⟩
    rintro _ ⟨⟨t, u⟩, ⟨ht, _⟩, rfl⟩
    have hz : e (Φ (t - τ) (η u)) ∈ e ''
        ((fun q : ℝ × M => Φ q.1 q.2) ''
          (Ioo (-d) d ×ˢ (N ∩ {x | (e x).2 = ell + τ}))) :=
      ⟨Φ (t - τ) (η u), ⟨(t - τ, η u),
        ⟨htime t ht, hηN (mem_range_self u), congrArg Prod.snd (hηeq u)⟩, rfl⟩, rfl⟩
    rw [hVe] at hz
    exact hz.1

theorem isCutPair_of_level_arc
    {M : Type*} [TopologicalSpace M]
    {e : M → Schoenflies.Plane × ℝ} (he : Continuous e) (hei : Function.Injective e)
    {η : unitInterval → M} (hη : Continuous η) (hηi : Function.Injective η)
    {a : ℝ} (hlevel : ∀ t, (e (η t)).2 = a) {p : M}
    (hbase : η 0 ∈ connectedComponentIn {x | a ≤ (e x).2} p)
    {C : Set Schoenflies.Plane} (hC : Schoenflies.IsJordanCurve C)
    (hcircle : (fun x => (e x).1) ''
      (connectedComponentIn {x | a ≤ (e x).2} p ∩ {x | (e x).2 = a}) = C)
    {A : Set Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A (e (η 0)).1 (e (η 1)).1)
    (hAsub : A ⊆ C)
    (hne : ∃ z ∈ A, z ∉ range (fun t => (e (η t)).1)) :
    Schoenflies.IsCutPair C (e (η 0)).1 (e (η 1)).1 A
      (range (fun t => (e (η t)).1)) := by
  have hcomponent : range η ⊆ connectedComponentIn {x | a ≤ (e x).2} p := by
    rw [connectedComponentIn_eq hbase]
    apply (isPreconnected_range hη).subset_connectedComponentIn (mem_range_self (0 : unitInterval))
    rintro _ ⟨t, rfl⟩
    exact (hlevel t).ge
  have hsub : range (fun t => (e (η t)).1) ⊆ C := by
    rintro _ ⟨t, rfl⟩
    rw [← hcircle]
    exact ⟨η t, ⟨hcomponent (mem_range_self t), hlevel t⟩, rfl⟩
  have hemb : _root_.Topology.IsEmbedding (fun t => (e (η t)).1) := by
    apply ((he.comp hη).fst.isClosedEmbedding ?_).isEmbedding
    intro t u htu
    apply hηi
    apply hei
    exact Prod.ext htu ((hlevel t).trans (hlevel u).symm)
  have harc := Schoenflies.isArcBetween_range_of_isEmbedding hemb
  obtain ⟨A₀, A₁, hcut₀⟩ := Schoenflies.exists_isCutPair hC
    (hAsub hA.left_mem) (hAsub hA.right_mem) hA.ne
  have hcutA : ∃ B, Schoenflies.IsCutPair C (e (η 0)).1 (e (η 1)).1 A B := by
    rcases hA.eq_fst_or_eq_snd_of_subset hAsub hcut₀ with h | h
    · exact ⟨A₁, h.symm ▸ hcut₀⟩
    · exact ⟨A₀, h.symm ▸ hcut₀.symm⟩
  obtain ⟨B, hcut⟩ := hcutA
  rcases harc.eq_fst_or_eq_snd_of_subset hsub hcut with h | h
  · obtain ⟨z, hzA, hz⟩ := hne
    exact False.elim (hz (h.symm ▸ hzA))
  · simpa only [h] using hcut

theorem exists_diffeomorph_height_cap_component_level
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p : SphereTwo} {a r : ℝ} (hr : 0 < r) (hab : a ≤ e p 2 - r ^ 2 / 2)
    (hregular : ∀ x, e x 2 ∈ Ico a (e p 2) →
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (A : ((EuclideanSpace ℝ (Fin 2)) × ℝ) ≃ₘ[ℝ] ((EuclideanSpace ℝ (Fin 2)) × ℝ))
    (hA : ∀ z, (A z).2 = z.2)
    (hcap : (EuclideanSpace.equivProdLast 2 ∘ e) ''
      connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
        (fun y => A (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r)
    (Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)))
    (hΦ : Continuous (fun z : ℝ × (EuclideanSpace ℝ (Fin 2)) => Φ z.1 z.2))
    (hΦa : Φ a = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞)
    (hlevels : ∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
      Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = a}) =
        (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t})
    {t : ℝ} (ht : t ∈ Icc a (e p 2 - r ^ 2 / 2)) :
    ∃ G : (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
      (G : (EuclideanSpace ℝ (Fin 2)) → (EuclideanSpace ℝ (Fin 2))) =
        (fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm (A (y, e p 2 - r ^ 2 / 2)).1)) ∧
      (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
        (connectedComponentIn {x | t ≤ e x 2} p ∩ {x | e x 2 = t}) = G '' sphere 0 r := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hbp : e p 2 - r ^ 2 / 2 < e p 2 := by nlinarith [sq_pos_of_pos hr]
  have hboundary := image_superlevel_component_level_eq_sphere_of_quadratic_cap
    (e := L ∘ e) (I := 𝓡 2) (c := e p 2) (α := -1)
    (L.toHomeomorph.isEmbedding.comp he.isEmbedding) hf hab
    (by ring) (by norm_num) hr.le
    (isClosed_Icc.preimage hf.continuous).isCompact
    (fun x hx => hregular x ⟨hx.1, hx.2.trans_lt hbp⟩) hbp.le A hA hcap
    (fun v => (Φ v).toEquiv)
    (fun x _ => (hΦ.comp (continuous_id.prodMk continuous_const)).continuousOn)
    (by intro y _; change Φ a y = y; rw [hΦa]; rfl) hlevels
  let Ap : ((EuclideanSpace ℝ (Fin 2)) × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ),
      (𝓡 2).prod 𝓘(ℝ)⟯ ((EuclideanSpace ℝ (Fin 2)) × ℝ) :=
    { toEquiv := A.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.symm.contMDiff }
  let G := (Ap.restrictFiber hA (e p 2 - r ^ 2 / 2)).trans
    ((Φ (e p 2 - r ^ 2 / 2)).symm.trans (Φ t))
  exact ⟨G, rfl, hboundary t ht⟩

theorem isCutPair_of_height_cap_level_arc
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p : SphereTwo} {a r : ℝ} (hr : 0 < r) (hab : a ≤ e p 2 - r ^ 2 / 2)
    (hregular : ∀ x, e x 2 ∈ Ico a (e p 2) →
      ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (A : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ))
    (hA : ∀ z, (A z).2 = z.2)
    (hcap : (EuclideanSpace.equivProdLast 2 ∘ e) ''
      connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
        (fun y => A (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' closedBall 0 r)
    (Φ : ℝ → Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
    (hΦ : Continuous (fun z : ℝ × Schoenflies.Plane => Φ z.1 z.2))
    (hΦa : Φ a = Diffeomorph.refl (𝓡 2) Schoenflies.Plane ∞)
    (hlevels : ∀ t ∈ Icc a (e p 2 - r ^ 2 / 2),
      Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = a}) =
        (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t})
    {t : ℝ} (ht : t ∈ Icc a (e p 2 - r ^ 2 / 2))
    {η : unitInterval → SphereTwo} (hη : Continuous η) (hηi : Function.Injective η)
    (hlevel : ∀ u, e (η u) 2 = t)
    {Arc : Set Schoenflies.Plane}
    (hArc : Schoenflies.IsArcBetween Arc
      (EuclideanSpace.equivProdLast 2 (e (η 0))).1
      (EuclideanSpace.equivProdLast 2 (e (η 1))).1)
    (hselected : Arc ⊆ (fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
      (A (y, e p 2 - r ^ 2 / 2)).1)) '' sphere 0 r)
    (hne : ∃ z ∈ Arc, z ∉ range (fun u => (EuclideanSpace.equivProdLast 2 (e (η u))).1)) :
    Schoenflies.IsCutPair
      ((fun y => Φ t ((Φ (e p 2 - r ^ 2 / 2)).symm
        (A (y, e p 2 - r ^ 2 / 2)).1)) '' sphere 0 r)
      (EuclideanSpace.equivProdLast 2 (e (η 0))).1
      (EuclideanSpace.equivProdLast 2 (e (η 1))).1 Arc
      (range (fun u => (EuclideanSpace.equivProdLast 2 (e (η u))).1)) := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  have heL := L.toHomeomorph.isEmbedding.comp he.isEmbedding
  obtain ⟨G, hG, hboundary⟩ := exists_diffeomorph_height_cap_component_level
    he hr hab hregular A hA hcap Φ hΦ hΦa hlevels ht
  have hC : Schoenflies.IsJordanCurve (G '' sphere 0 r) :=
    PlanarJordan.isJordanCurve_image_sphere G.toHomeomorph 0 hr
  rw [hG] at hC hboundary
  have hbase : η 0 ∈ connectedComponentIn {x | t ≤ e x 2} p := by
    have hm := hselected hArc.left_mem
    obtain ⟨x, ⟨hx, hxlevel⟩, hxeq⟩ := hboundary.symm.subset hm
    have hxη : x = η 0 := heL.injective
      (Prod.ext hxeq (hxlevel.trans (hlevel 0).symm))
    exact hxη ▸ hx
  exact isCutPair_of_level_arc heL.continuous heL.injective hη hηi
    hlevel hbase hC hboundary hArc hselected hne

theorem range_eq_sdiff_image_saddleBandLevelCurve
    {X P : Type*} {γ : X → P} {B : (ℝ × ℝ) → P}
    (hB : Function.Injective B) {s τ σ h : ℝ} {C : Set P}
    (hunion : B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∪ range γ = C)
    (hinter : B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∩ range γ =
      {B (saddleBandLevelCurve s τ σ (-h)), B (saddleBandLevelCurve s τ σ h)}) :
    range γ = C \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) := by
  have hinj : Function.Injective (fun u => B (saddleBandLevelCurve s τ σ u)) := by
    intro u v huv
    exact congrArg Prod.fst (hB huv)
  have hdiff : B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h) =
      (B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h)) \ range γ := by
    simp only [image_image] at hinj ⊢
    rw [← Icc_sdiff_both, image_sdiff hinj, image_pair]
    rw [← image_image, ← hinter]
    ext y
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff, ← hunion]
  ext y
  simp only [mem_sdiff, mem_union]
  tauto

theorem range_lift_eq_sdiff_image_saddleBandLevelCurve
    {M X P : Type*} {e : M → P × ℝ} (he : Function.Injective e)
    {η : X → M} {γ : X → P} {B : (ℝ × ℝ) → P}
    (hB : Function.Injective B) {s τ σ h a : ℝ} {C : Set P}
    (heq : ∀ u, e (η u) = (γ u, a))
    (hunion : B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∪ range γ = C)
    (hinter : B '' (saddleBandLevelCurve s τ σ '' Icc (-h) h) ∩ range γ =
      {B (saddleBandLevelCurve s τ σ (-h)), B (saddleBandLevelCurve s τ σ h)}) :
    range η = {x | (e x).2 = a ∧ (e x).1 ∈
      C \ B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h)} := by
  have hγ := range_eq_sdiff_image_saddleBandLevelCurve hB hunion hinter
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_ofPred_eq, heq]
    exact ⟨rfl, hγ ▸ mem_range_self u⟩
  · rintro ⟨hx, hxc⟩
    rw [← hγ] at hxc
    obtain ⟨u, hu⟩ := hxc
    refine ⟨u, he ?_⟩
    rw [heq, hu, ← hx]

theorem exists_open_endpoint_saddleBandLevelCurve_transport
    {M : Type*} [TopologicalSpace M] {e : M → Schoenflies.Plane × ℝ}
    {η : unitInterval → M} (hη : Continuous η)
    {γ : unitInterval → Schoenflies.Plane} (hγ : Continuous γ)
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane) (G : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {s τ σ c h k R r D : ℝ} (hs : 0 ≤ s) (hσ : σ ^ 2 = 1)
    (hh : 0 ≤ h) (hk : k < 1) (hr : 0 < r) (hD : 0 < D) (hDsh : D < τ + s * h ^ 2)
    (heq : ∀ u, e (η u) = (γ u, c + s + τ))
    (hγ0 : γ 0 = B (saddleBandLevelCurve s τ σ (-h)))
    (hγ1 : γ 1 = B (saddleBandLevelCurve s τ σ h))
    (hend0 : saddleBandLevelCurve s τ σ (-h) ∈ Ioo (-k) k ×ˢ Ioo (-R) R)
    (hend1 : saddleBandLevelCurve s τ σ h ∈ Ioo (-k) k ×ˢ Ioo (-R) R)
    (hside : ∀ z ∈ Ioo (-k) k ×ˢ Ioo (-R) R,
      (B z ∈ interior (G '' closedBall 0 r) ↔
        c + s + τ < c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2) ∧
      (B z ∈ G '' closedBall 0 r ↔
        c + s + τ ≤ c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 ∧ 0 < σ * z.2))
    (hsub : range γ ⊆ (G '' sphere 0 r) \
      B '' (saddleBandLevelCurve s τ σ '' Ioo (-h) h))
    {P : Set M} (hP : IsOpen P) (hη0 : η 0 ∈ P) (hη1 : η 1 ∈ P)
    (Φ : ℝ → M → M) (hΦ0 : ∀ x, Φ 0 x = x)
    (hflow : ∀ x ∈ P, IsIntegralCurveOn (fun t => B.symm (e (Φ t x)).1)
      (fun _ => saddleBandVectorField) (Icc (-D) D))
    (hreg : ∀ x ∈ P, ∀ t ∈ Icc (-D) D,
      (1 - (B.symm (e (Φ t x)).1).1 ^ 2) * (B.symm (e (Φ t x)).1).2 ≠ 0) :
    ∃ W : Set unitInterval, IsOpen W ∧ (0 : unitInterval) ∈ W ∧ (1 : unitInterval) ∈ W ∧
      W ⊆ η ⁻¹' P ∧
      ∀ u ∈ W,
        B.symm (γ u) ∈ Ioo (-k) k ×ˢ Ioo (-R) R ∧
        h ^ 2 ≤ (B.symm (γ u)).1 ^ 2 ∧
        γ u = B (saddleBandLevelCurve s τ σ (B.symm (γ u)).1) ∧
        ∀ t ∈ Icc (-D) D,
          (e (Φ t (η u))).1 = B (saddleBandLevelCurve s (τ + t) σ (B.symm (γ u)).1) := by
  let W := η ⁻¹' P ∩ (fun u => B.symm (γ u)) ⁻¹' (Ioo (-k) k ×ˢ Ioo (-R) R)
  have hW : IsOpen W := (hP.preimage hη).inter
    ((isOpen_Ioo.prod isOpen_Ioo).preimage (B.symm.continuous.comp hγ))
  have hzero : (0 : unitInterval) ∈ W := by
    refine ⟨hη0, ?_⟩
    change B.symm (γ 0) ∈ Ioo (-k) k ×ˢ Ioo (-R) R
    rw [hγ0, B.symm_apply_apply]
    exact hend0
  have hone : (1 : unitInterval) ∈ W := by
    refine ⟨hη1, ?_⟩
    change B.symm (γ 1) ∈ Ioo (-k) k ×ˢ Ioo (-R) R
    rw [hγ1, B.symm_apply_apply]
    exact hend1
  refine ⟨W, hW, hzero, hone, inter_subset_left, ?_⟩
  intro u hu
  let z := B.symm (γ u)
  have hz : z ∈ Ioo (-k) k ×ˢ Ioo (-R) R := hu.2
  have hκ : z = saddleBandLevelCurve s τ σ z.1 :=
    PlanarJordan.eq_saddleBandLevelCurve_of_mem_image_sphere B G hσ hk hr hside hz
      (by simpa only [z, B.apply_symm_apply] using (hsub (mem_range_self u)).1)
  have hnot : z.1 ∉ Ioo (-h) h := by
    intro hin
    exact (hsub (mem_range_self u)).2 ⟨z, ⟨z.1, hin, hκ.symm⟩, B.apply_symm_apply _⟩
  have hsquare : h ^ 2 ≤ z.1 ^ 2 := by
    by_contra hn
    apply hnot
    constructor <;> nlinarith
  have hinit : B.symm (e (Φ 0 (η u))).1 = saddleBandLevelCurve s τ σ z.1 := by
    rw [hΦ0, heq]
    exact hκ
  have htime : D < τ + s * z.1 ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsquare hs
    linarith
  have heqcurve := eq_saddleBandLevelCurve_of_isIntegralCurveOn hD
    (hflow (η u) hu.1) (hreg (η u) hu.1) hinit htime hσ
    (show z.1 ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith [hz.1.1, hz.1.2])
  refine ⟨hz, hsquare, ?_, ?_⟩
  · exact (B.apply_symm_apply _).symm.trans (congrArg B hκ)
  · intro t ht
    have hh := congrArg B (heqcurve ht)
    simpa only [B.apply_symm_apply] using hh

theorem exists_height_preserving_diffeomorph_of_transported_level_arc
    {M : Type*} {f : M → Schoenflies.Plane × ℝ}
    {η : unitInterval → M} {γ : unitInterval → Schoenflies.Plane}
    {Φ : ℝ → M → M} {ell δ τ h ρ : ℝ}
    (hτ : τ ∈ Icc (-δ) δ) (hzero : ∀ x, Φ 0 x = x)
    (hinitial : ∀ u, f (η u) = (γ u, ell + τ))
    (hfamily : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Schoenflies.Plane) ∞
      (fun q : ℝ × unitInterval => (f (Φ (q.1 - τ) (η q.2))).1)
      (Icc (-δ) δ ×ˢ univ))
    (hslices : ∀ t ∈ Icc (-δ) δ, IsSmoothEmbedding (𝓡∂ 1)
      𝓘(ℝ, Schoenflies.Plane) ∞ (fun u => (f (Φ (t - τ) (η u))).1))
    (hheight : ∀ t ∈ Icc (-δ) δ, ∀ u, (f (Φ (t - τ) (η u))).2 = ell + t)
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane)
    (havoid : ∀ t ∈ Icc (-δ) δ, ∀ u,
      B.symm (f (Φ (t - τ) (η u))).1 ∉ Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ)
    {W : Set ℝ} (hW : IsOpen W) (hIW : Icc (ell - δ) (ell + δ) ⊆ W) :
    ∃ D : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ),
      (∀ y, (D y).2 = y.2) ∧
      (∀ y, D (y, ell + τ) = (y, ell + τ)) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ u, D (γ u, ell + t) = f (Φ (t - τ) (η u))) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ u, D.symm (f (Φ (t - τ) (η u))) = (γ u, ell + t)) ∧
      D '' (range γ ×ˢ Icc (ell - δ) (ell + δ)) =
        (fun q : ℝ × unitInterval => f (Φ (q.1 - τ) (η q.2))) ''
          (Icc (-δ) δ ×ˢ univ) ∧
      ∃ K : Set (Schoenflies.Plane × ℝ), IsCompact K ∧
        K ⊆ (B '' (Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ))ᶜ ×ˢ W ∧
        EqOn D id Kᶜ ∧ EqOn D.symm id Kᶜ := by
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) unitInterval :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) unitInterval)
  let _ : IsManifold (𝓡∂ (0 + 1)) ∞ unitInterval :=
    inferInstanceAs (IsManifold (𝓡∂ 1) ∞ unitInterval)
  let ζ : ℝ × unitInterval → Schoenflies.Plane :=
    fun q => (f (Φ (q.1 - ell - τ) (η q.2))).1
  have hshift : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) (𝓘(ℝ).prod (𝓡∂ 1)) ∞
      (fun q : ℝ × unitInterval => (q.1 - ell, q.2)) :=
    (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
  have hshiftmem {z : ℝ} (hz : z ∈ Icc (ell - δ) (ell + δ)) :
      z - ell ∈ Icc (-δ) δ := by constructor <;> linarith [hz.1, hz.2]
  have hζ : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Schoenflies.Plane) ∞ ζ
      (Icc (ell - δ) (ell + δ) ×ˢ univ) :=
    hfamily.comp hshift.contMDiffOn (fun _ hz => ⟨hshiftmem hz.1, mem_univ _⟩)
  have hζemb (z : ℝ) (hz : z ∈ Icc (ell - δ) (ell + δ)) :
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ (fun u => ζ (z, u)) :=
    hslices (z - ell) (hshiftmem hz)
  have hcore : IsCompact (B '' (Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ)) :=
    (isCompact_Icc.prod isCompact_Icc).image B.continuous
  have hζavoid : ζ '' (Icc (ell - δ) (ell + δ) ×ˢ univ) ⊆
      (B '' (Icc (-(h / 2)) (h / 2) ×ˢ Icc (-ρ) ρ))ᶜ := by
    rintro _ ⟨⟨z, u⟩, ⟨hz, _⟩, rfl⟩ ⟨w, hw, heq⟩
    apply havoid (z - ell) (hshiftmem hz) u
    change B.symm (ζ (z, u)) ∈ _
    simpa only [← heq, B.symm_apply_apply] using hw
  have hc : ell + τ ∈ Icc (ell - δ) (ell + δ) := by
    constructor <;> linarith [hτ.1, hτ.2]
  obtain ⟨D, hDheight, hDfix, hDζ, _, K, hK, hKsub, hKid⟩ :=
    exists_height_preserving_diffeomorph_of_halfspace_level_family_at
      hc hζ hζemb hcore.isClosed.isOpen_compl hζavoid hW hIW
  have hζbase (u : unitInterval) : ζ (ell + τ, u) = γ u := by
    dsimp [ζ]
    rw [show ell + τ - ell - τ = 0 by ring, hzero, hinitial]
  have hforward (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) :
      D (γ u, ell + t) = f (Φ (t - τ) (η u)) := by
    have hzt : ell + t ∈ Icc (ell - δ) (ell + δ) := by
      constructor <;> linarith [ht.1, ht.2]
    have heq := hDζ (ell + t) hzt u
    rw [hζbase] at heq
    convert heq using 1
    apply Prod.ext
    · simp [ζ]
    · exact hheight t ht u
  refine ⟨D, hDheight, hDfix, hforward, ?_, ?_, K, hK, hKsub, hKid, ?_⟩
  · intro t ht u
    rw [← hforward t ht u, D.symm_apply_apply]
  · ext z
    constructor
    · rintro ⟨⟨y, t⟩, ⟨⟨u, rfl⟩, ht⟩, rfl⟩
      refine ⟨(t - ell, u), ⟨hshiftmem ht, mem_univ _⟩, ?_⟩
      simpa only [add_sub_cancel] using (hforward (t - ell) (hshiftmem ht) u).symm
    · rintro ⟨⟨t, u⟩, ⟨ht, _⟩, rfl⟩
      refine ⟨(γ u, ell + t), ⟨mem_range_self u, ?_⟩, hforward t ht u⟩
      constructor <;> linarith [ht.1, ht.2]
  · intro x hx
    apply D.injective
    change D (D.symm x) = D x
    rw [D.apply_symm_apply, hKid hx]
    rfl

end DifferentialGeometry.Topology.SphereSeparation
