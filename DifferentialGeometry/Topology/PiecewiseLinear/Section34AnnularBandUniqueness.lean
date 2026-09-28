import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandTargetTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.exists_continuous_lateral_parametrization {M : Type*}
    [TopologicalSpace M] {A A₀ A₁ : Set M} (hA : IsAnnulusOn A A₀ A₁) :
    ∃ f : (Fin 3 → ℝ) × ℝ → M,
      ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ∧
      f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = A ∧
      f '' (stdSimplexBoundary 2 ×ˢ {0}) = A₀ ∧
      f '' (stdSimplexBoundary 2 ×ˢ {1}) = A₁ := by
  classical
  obtain ⟨e, he₀, he₁⟩ := isAnnulusOn_stdSimplex_lateral
  obtain ⟨φ, hφ₀, hφ₁⟩ := hA
  let ψ := e.symm.trans φ
  obtain ⟨a, -⟩ := (IsAnnulusOn.isConnected ⟨φ, hφ₀, hφ₁⟩).nonempty
  let f : (Fin 3 → ℝ) × ℝ → M := Function.extend Subtype.val
    (fun p => (ψ p).val) (fun _ => a)
  have hfe (p : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :
      f p.val = (ψ p).val :=
    Function.Injective.extend_apply Subtype.val_injective _ _ p
  have hfc : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp ψ.continuous using 1
    funext p
    exact hfe p
  have hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hp := ψ.injective (Subtype.ext ((hfe ⟨x, hx⟩).symm.trans
      (hxy.trans (hfe ⟨y, hy⟩))))
    exact congrArg Subtype.val hp
  have hfull : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = A := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [hfe ⟨p, hp⟩]
      exact (ψ ⟨p, hp⟩).property
    · intro x hx
      refine ⟨(ψ.symm ⟨x, hx⟩).val, (ψ.symm ⟨x, hx⟩).property, ?_⟩
      rw [hfe, ψ.apply_symm_apply]
  have hlevel (X : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × unitInterval)) :
      f '' (Subtype.val '' (e '' X)) = Subtype.val '' (φ '' X) := by
    rw [image_image, image_image, image_image]
    apply image_congr
    intro p _
    rw [hfe]
    change (φ (e.symm (e p))).val = (φ p).val
    rw [e.symm_apply_apply]
  exact ⟨f, hfc, hfi, hfull, he₀.symm ▸ (hlevel _).trans hφ₀.symm,
    he₁.symm ▸ (hlevel _).trans hφ₁.symm⟩

private theorem lateral_band_eq_of_disjoint_caps {M : Type*}
    [TopologicalSpace M] [T2Space M] {B J K D₀ D₁ : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B]
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hgB : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = K)
    (hg₀ : g '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hg₁ : g '' (stdSimplexBoundary 2 ×ˢ {1}) = K)
    (hD₀ : IsClosed D₀) (hD₁ : IsClosed D₁) (hdis : Disjoint D₀ D₁)
    (hcover : B ⊆ D₀ ∪ D₁ ∪ g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hcap₀ : (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₀ = J)
    (hcap₁ : (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₁ = K) :
    f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  let D := f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
  let F := g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
  let O := f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
  let V := g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
  change D = F
  have hO : O = D \ (J ∪ K) := by
    dsimp only [O, D]
    rw [image_lateral_open_eq_sdiff_ends hfi, hf₀, hf₁]
  have hV : V = F \ (J ∪ K) := by
    dsimp only [V, F]
    rw [image_lateral_open_eq_sdiff_ends hgi, hg₀, hg₁]
  have hclO : closure O = D := closure_image_lateral_open hf
  have hclV : closure V = F := closure_image_lateral_open hg
  have hconn := (isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))
  have hOc : IsConnected O := hconn.image f (hf.mono (prod_mono_right Ioo_subset_Icc_self))
  have hVc : IsConnected V := hconn.image g (hg.mono (prod_mono_right Ioo_subset_Icc_self))
  have hannD := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hf hfi
  have hannF := isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hg hgi
  rw [hf₀, hf₁] at hannD
  rw [hg₀, hg₁] at hannF
  have hFc : IsClosed F := hannF.isCompact.isClosed
  have hOF : O ⊆ F := by
    have hside₀ : O ⊆ D₁ ∪ F := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hOc.isPreconnected D₀ (D₁ ∪ F)
        hD₀ (hD₁.union hFc) (by
          intro x hx
          rcases hcover (hfB (hO.subset hx).1) with (hx₀ | hx₁) | hxF
          · exact Or.inl hx₀
          · exact Or.inr (Or.inl hx₁)
          · exact Or.inr (Or.inr hxF))
        (by
          apply disjoint_iff_inter_eq_empty.mp
          refine disjoint_left.mpr fun x hx hxcap => ?_
          rw [hO] at hx
          rcases hxcap.2 with hx₁ | hxF
          · exact disjoint_left.mp hdis hxcap.1 hx₁
          · exact hx.2 (Or.inl (hcap₀.subset ⟨hxF, hxcap.1⟩))) with h | h
      · have hDsub : D ⊆ D₀ := hclO ▸ closure_minimal h hD₀
        obtain ⟨x, hx⟩ := hannD.ends_nonempty.2
        exact (disjoint_left.mp hdis (hDsub (hannD.second_subset hx))
          (hcap₁.superset hx).2).elim
      · exact h
    have hside₁ : O ⊆ D₀ ∪ F := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp hOc.isPreconnected D₁ (D₀ ∪ F)
        hD₁ (hD₀.union hFc) (by
          intro x hx
          rcases hcover (hfB (hO.subset hx).1) with (hx₀ | hx₁) | hxF
          · exact Or.inr (Or.inl hx₀)
          · exact Or.inl hx₁
          · exact Or.inr (Or.inr hxF))
        (by
          apply disjoint_iff_inter_eq_empty.mp
          refine disjoint_left.mpr fun x hx hxcap => ?_
          rw [hO] at hx
          rcases hxcap.2 with hx₀ | hxF
          · exact disjoint_left.mp hdis hx₀ hxcap.1
          · exact hx.2 (Or.inr (hcap₁.subset ⟨hxF, hxcap.1⟩))) with h | h
      · have hDsub : D ⊆ D₁ := hclO ▸ closure_minimal h hD₁
        obtain ⟨x, hx⟩ := hannD.ends_nonempty.1
        exact (disjoint_left.mp hdis (hcap₀.superset hx).2
          (hDsub (hannD.first_subset hx))).elim
      · exact h
    intro x hx
    rcases hside₀ hx with hx₁ | hxF
    · rcases hside₁ hx with hx₀ | hxF
      · exact (disjoint_left.mp hdis hx₀ hx₁).elim
      · exact hxF
    · exact hxF
  have hDF : D ⊆ F := hclO ▸ closure_minimal hOF hFc
  have hVD : V ⊆ D := by
    apply hannD.subset_of_isPreconnected_of_disjoint_boundary_within hfB
      (fun _ hx => hgB (hV.subset hx).1) hVc.isPreconnected
    · obtain ⟨x, hx⟩ := hOc.nonempty
      have hxD := (hO.subset hx).1
      exact ⟨x, hV.superset ⟨hDF hxD, (hO.subset hx).2⟩, hxD⟩
    · rw [hV]
      exact disjoint_sdiff_left
  exact Subset.antisymm hDF (hclV ▸ closure_minimal hVD hannD.isCompact.isClosed)

theorem IsPLSphere.image_lateral_eq_of_same_ends {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S A A₀ A₁ J K : Set E}
    (hS : IsPLSphere 2 S) (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S)
    (hJ : IsPLSphere 1 J) (hK : IsPLSphere 1 K) (hJA : J ⊆ A) (hKA : K ⊆ A)
    (hJK : Disjoint J K) (hJend : Disjoint J (A₀ ∪ A₁))
    (hKend : Disjoint K (A₀ ∪ A₁))
    (hJess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J)
    (hKess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = K)
    {f g : (Fin 3 → ℝ) × ℝ → E}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfA : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hgA : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = K)
    (hg₀ : g '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hg₁ : g '' (stdSimplexBoundary 2 ×ˢ {1}) = K) :
    f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨D₀, D₁, r₀, r₁, φ, hr₀, hr₁, -, -, -, -, hdis, -, hφ, hφA,
    hφ₀, hφ₁, hcap₀, hcap₁, hcover⟩ :=
    hS.exists_annular_band_with_end_caps hA hAS hJ hK hJA hKA hJK hJend hKend hJess hKess
  obtain ⟨hc⟩ := hS.nonempty_chartedSpace_two
  let _ := hc
  have h₀ := (IsPLBall.isPolyhedron ⟨r₀, hr₀⟩).isClosed
  have h₁ := (IsPLBall.isPolyhedron ⟨r₁, hr₁⟩).isClosed
  have hcompare {k : (Fin 3 → ℝ) × ℝ → E}
      (hk : ContinuousOn k (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (hki : InjOn k (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (hkA : k '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
      (hk₀ : k '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
      (hk₁ : k '' (stdSimplexBoundary 2 ×ˢ {1}) = K) :
      k '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
        φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    lateral_band_eq_of_disjoint_caps hk hki hφ.isPiecewiseAffineOn.continuousOn
      hφ.bijOn.injOn (hkA.trans hAS) (hφA.trans hAS) hk₀ hk₁ hφ₀ hφ₁
      h₀ h₁ hdis hcover hcap₀ hcap₁
  exact (hcompare hf hfi hfA hf₀ hf₁).trans (hcompare hg hgi hgA hg₀ hg₁).symm

theorem IsPLCellOn.image_lateral_eq_of_same_ends {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J L : Set M} (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁)
    (hAB : A ⊆ B) (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hL : IsPolyhedralSphere (n := 3) 1 L) (hJA : J ⊆ A) (hLA : L ⊆ A)
    (hJL : Disjoint J L) (hJend : Disjoint J (A₀ ∪ A₁))
    (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A)
    (hLess : ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A)
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfA : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hgA : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hf₀ : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hf₁ : f '' (stdSimplexBoundary 2 ×ˢ {1}) = L)
    (hg₀ : g '' (stdSimplexBoundary 2 ×ˢ {0}) = J)
    (hg₁ : g '' (stdSimplexBoundary 2 ×ˢ {1}) = L) :
    f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hfront : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [hr.image_stdSimplexBoundary_eq_frontier] at hB
  have hAP : A ⊆ u '' P := hAB.trans (hB ▸ image_mono hfront)
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hτc : ContinuousOn τ (u '' P) := (hu.isPLOn_inverse hleft).continuousOn
  have hτi : InjOn τ (u '' P) := by
    intro x hx y hy hxy
    rw [← hright hx, ← hright hy, hxy]
  have hA' := hA.image_of_continuousOn_injOn (hτc.mono hAP) (hτi.mono hAP)
  have hA'S : τ '' A ⊆ frontier P := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hAB hx
    rw [hleft (hfront hz)]
    exact hz
  have hback (X : Set M) (hXA : X ⊆ A) : u '' (τ '' X) = X := by
    rw [image_image]
    exact (image_congr fun x hx => hright (hAP (hXA hx))).trans (image_id' X)
  have hdisj {X Y : Set M} (hXA : X ⊆ A) (hYA : Y ⊆ A) (hXY : Disjoint X Y) :
      Disjoint (τ '' X) (τ '' Y) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq := hτi (hAP (hXA hx)) (hAP (hYA hy)) hxy.symm
    exact disjoint_left.mp hXY hx (heq ▸ hy)
  have hess {X : Set M} (hXA : X ⊆ A)
      (hXess : ¬ ∃ D : Set M, IsPLCellOn 2 D X ∧ D ⊆ A) :
      ¬ ∃ (D : Set (EuclideanSpace ℝ (Fin 3)))
        (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ τ '' A ∧
          q '' stdSimplexBoundary 2 = τ '' X := by
    rintro ⟨D, q, hq, hDA, hqb⟩
    have hDP := (hDA.trans hA'S).trans hfront
    have hpoly : IsPolyhedron D := IsPLBall.isPolyhedron ⟨q, hq⟩
    have huD : IsPLHomeomorphInto 3 u D :=
      (hu.isPLOn.mono_of_isPolyhedron hpoly hDP).isPLHomeomorphInto_model
        hpoly.isCompact (hu.injOn.mono hDP)
    have hc := (isPLCellOn_id_of_isPLBall hq).image huD
    rw [hqb, hback X hXA] at hc
    exact hXess ⟨u '' D, hc, hback A Subset.rfl ▸ image_mono hDA⟩
  have hendA := union_subset hA.first_subset hA.second_subset
  have hfmap : MapsTo f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (u '' P) :=
    fun x hx => hAP (hfA ⟨x, hx, rfl⟩)
  have hgmap : MapsTo g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) (u '' P) :=
    fun x hx => hAP (hgA ⟨x, hx, rfl⟩)
  have heq := hP.isPLSphere_frontier.image_lateral_eq_of_same_ends hA' hA'S
    (hu.isPLSphere_invFunOn_image hJ (hJA.trans hAP))
    (hu.isPLSphere_invFunOn_image hL (hLA.trans hAP))
    (image_mono hJA) (image_mono hLA) (hdisj hJA hLA hJL)
    (by rw [← image_union]; exact hdisj hJA hendA hJend)
    (by rw [← image_union]; exact hdisj hLA hendA hLend)
    (hess hJA hJess) (hess hLA hLess)
    (hτc.comp hf hfmap) (fun x hx y hy hxy => hfi hx hy (hτi (hfmap hx) (hfmap hy) hxy))
    (hτc.comp hg hgmap) (fun x hx y hy hxy => hgi hx hy (hτi (hgmap hx) (hgmap hy) hxy))
    (by rw [image_comp]; exact image_mono hfA)
    (by rw [image_comp]; exact image_mono hgA)
    (by rw [image_comp, hf₀]) (by rw [image_comp, hf₁])
    (by rw [image_comp, hg₀]) (by rw [image_comp, hg₁])
  rw [image_comp, image_comp] at heq
  have hout := congrArg (fun X => u '' X) heq
  rwa [hback _ hfA, hback _ hgA] at hout

theorem IsPLCellOn.annulus_eq_of_same_essential_ends {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B A A₀ A₁ J L D F : Set M} (hS : IsPLCellOn 3 S B)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hL : IsPolyhedralSphere (n := 3) 1 L)
    (hJA : J ⊆ A) (hLA : L ⊆ A) (hJL : Disjoint J L)
    (hJend : Disjoint J (A₀ ∪ A₁)) (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ D : Set M, IsPLCellOn 2 D J ∧ D ⊆ A)
    (hLess : ¬ ∃ D : Set M, IsPLCellOn 2 D L ∧ D ⊆ A)
    (hD : IsAnnulusOn D J L) (hF : IsAnnulusOn F J L) (hDA : D ⊆ A) (hFA : F ⊆ A) :
    D = F := by
  obtain ⟨f, hf, hfi, hfD, hf₀, hf₁⟩ := hD.exists_continuous_lateral_parametrization
  obtain ⟨g, hg, hgi, hgF, hg₀, hg₁⟩ := hF.exists_continuous_lateral_parametrization
  rw [← hfD, ← hgF]
  exact hS.image_lateral_eq_of_same_ends hA hAB hJ hL hJA hLA hJL hJend hLend
    hJess hLess hf hfi hg hgi (hfD ▸ hDA) (hgF ▸ hFA) hf₀ hf₁ hg₀ hg₁

end DifferentialGeometry.Topology.PiecewiseLinear
