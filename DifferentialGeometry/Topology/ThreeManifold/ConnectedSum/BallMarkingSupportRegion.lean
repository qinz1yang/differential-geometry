import DifferentialGeometry.Topology.Manifold.AffineBallIsotopy
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingSupport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SumLaws

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

namespace BallMarking

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I]

def relativeSupportRegion (B B' : BallMarking M I) (V : I → Set E₃) : Prop :=
  (∀ i, IsOpen (V i)) ∧
    (∀ i, V i ⊆ (B'.ball i).chart.source) ∧
    (∀ i, Metric.closedBall (0 : E₃) 2 ⊆ V i) ∧
    (∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      (B.ball i).chart x ∈ (B'.ball i).chart '' V i) ∧
    (∀ i j, i ≠ j → Disjoint ((B'.ball i).chart '' V i) ((B'.ball j).chart '' V j))

def straightLineTube (B B' : BallMarking M I) (V : I → Set E₃) : Prop :=
  ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    (1 - t) • ((B'.ball i).chart.symm) ((B.ball i).chart (0 : E₃)) + t • (0 : E₃) ∈ V i

def orientationCompatible (B B' : BallMarking M I) : Prop :=
  ∀ i, 0 < (fderiv ℝ (fun x : E₃ => (B'.ball i).chart.symm ((B.ball i).chart x))
    (0 : E₃)).det

theorem orientationCompatible_self (B : BallMarking M I) : orientationCompatible B B := by
  intro i
  have h0 : (0 : E₃) ∈ (B.ball i).chart.source :=
    (B.ball i).closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hev : (fun x : E₃ => (B.ball i).chart.symm ((B.ball i).chart x)) =ᶠ[𝓝 (0 : E₃)] id :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E₃) (by norm_num : (0 : ℝ) < 2))
      fun x hx => PartialDiffeomorph.symm_apply_apply (B.ball i).chart
        ((B.ball i).closedBall_subset_source hx)
  rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_id]
  rw [show (ContinuousLinearMap.id ℝ E₃).det = 1 from map_one _]
  norm_num

theorem isotopic_of_relativeSupportRegion (B B' : BallMarking M I) {V : I → Set E₃}
    (hV : relativeSupportRegion B B' V) (htube : straightLineTube B B' V)
    (hori : orientationCompatible B B') : B.Isotopic B' := by
  classical
  obtain ⟨hopen, hVsrc, hballV, hsrcV, hdisjV⟩ := hV
  have hres_sub : ∀ i, (B.ball i).chart '' Metric.closedBall (0 : E₃) 2 ⊆
      (B'.ball i).chart '' V i := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hsrcV i x hx
  have hdata : ∀ i, ∃ (J : ℝ → Diffeomorph 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) E₃ E₃ ∞) (K : Set E₃),
      ContDiff ℝ ∞ (fun q : ℝ × E₃ => J q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E₃ => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl 𝓘(ℝ, E₃) E₃ ∞ ∧
      IsCompact K ∧ K ⊆ V i ∧
      (∀ t y, y ∉ K → J t y = y ∧ (J t).symm y = y) ∧
      (∀ x ∈ Metric.closedBall (0 : E₃) 2,
        J 1 ((B'.ball i).chart.symm ((B.ball i).chart x)) = x) := by
    intro i
    let φ₀ : PartialDiffeomorph 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) E₃ E₃ ∞ :=
      (B.ball i).chart.trans (B'.ball i).chart.symm
    let φ₁ : PartialDiffeomorph 𝓘(ℝ, E₃) 𝓘(ℝ, E₃) E₃ E₃ ∞ :=
      (Diffeomorph.refl 𝓘(ℝ, E₃) E₃ ∞).toPartialDiffeomorph
    have hφ₀coe : (φ₀ : E₃ → E₃) =
        fun x : E₃ => (B'.ball i).chart.symm ((B.ball i).chart x) := rfl
    have hφ₁coe : (φ₁ : E₃ → E₃) = id := rfl
    have himg_sub : (B'.ball i).chart '' V i ⊆ (B'.ball i).chart.target := by
      rintro y ⟨z, hz, rfl⟩
      exact (B'.ball i).chart.map_source (hVsrc i hz)
    have h₀ : Metric.closedBall (0 : E₃) 2 ⊆ φ₀.source := by
      intro x hx
      rw [PartialDiffeomorph.trans_source]
      refine ⟨(B.ball i).closedBall_subset_source hx, ?_⟩
      rw [PartialDiffeomorph.symm_source]
      exact himg_sub (hsrcV i x hx)
    have h₁ : Metric.closedBall (0 : E₃) 2 ⊆ φ₁.source := fun x _ => mem_univ x
    have hV₀ : φ₀ '' Metric.closedBall (0 : E₃) 2 ⊆ V i := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hsrcV i x hx
      rw [show ((B.ball i).chart.trans (B'.ball i).chart.symm) x
          = (B'.ball i).chart.symm ((B.ball i).chart x) from rfl,
        show (B'.ball i).chart.symm ((B.ball i).chart x) = z from by
          rw [← hzy]
          exact PartialDiffeomorph.symm_apply_apply (B'.ball i).chart (hVsrc i hz)]
      exact hz
    have hV₁ : φ₁ '' Metric.closedBall (0 : E₃) 2 ⊆ V i := by
      rintro y ⟨x, hx, rfl⟩
      exact hballV i hx
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • φ₀ 0 + t • φ₁ 0 ∈ V i := by
      intro t ht
      have h0 : φ₀ 0 = (B'.ball i).chart.symm ((B.ball i).chart (0 : E₃)) := rfl
      have h1 : φ₁ 0 = (0 : E₃) := rfl
      rw [h0, h1]
      exact htube i t ht
    have hdet₁ : (fderiv ℝ (φ₁ : E₃ → E₃) 0).det = 1 := by
      rw [hφ₁coe, fderiv_id]
      exact map_one _
    have hori' : 0 < (fderiv ℝ (φ₀ : E₃ → E₃) 0).det *
        (fderiv ℝ (φ₁ : E₃ → E₃) 0).det := by
      rw [hdet₁, mul_one, hφ₀coe]
      exact hori i
    obtain ⟨J, hJc, hJi, hJ0, hJact, K, hKc, hKV, hKfix⟩ :=
      Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset
        φ₀ φ₁ h₀ h₁ (hopen i) hV₀ hV₁ hseg hori'
    exact ⟨J, K, hJc, hJi, hJ0, hKc, hKV, hKfix, hJact⟩
  have hman : ∀ i, ∃ (J' : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
      (U : Set M.Carrier),
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M.Carrier => J' q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M.Carrier => (J' q.1).symm q.2) ∧
      J' 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞ ∧
      U ⊆ (B'.ball i).chart '' V i ∧
      (∀ t y, y ∉ U → J' t y = y ∧ (J' t).symm y = y) ∧
      (∀ x ∈ Metric.closedBall (0 : E₃) 2, J' 1 ((B.ball i).chart x) = (B'.ball i).chart x) := by
    intro i
    obtain ⟨J, K, hJc, hJi, hJ0, hKc, hKV, hKfix, hJact⟩ := hdata i
    have himg_sub : (B'.ball i).chart '' V i ⊆ (B'.ball i).chart.target := by
      rintro y ⟨z, hz, rfl⟩
      exact (B'.ball i).chart.map_source (hVsrc i hz)
    obtain ⟨J', hJ'c, hJ'i, hJ'form, -, -, hJ'fix⟩ :=
      Manifold.exists_diffeomorph_extension_of_partial_chart_family
        (P := ℝ) (B'.ball i).chart.symm.toOpenPartialHomeomorph
        (B'.ball i).chart.contMDiffOn_invFun (B'.ball i).chart.contMDiffOn_toFun
        J hJc hJi hKc (fun z hz => hVsrc i (hKV hz)) hKfix
    have hfix0 : J' 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞ := by
      apply Diffeomorph.ext
      intro y
      rw [(hJ'form 0 y).1, hJ0]
      by_cases hy : y ∈ (B'.ball i).chart.symm.toOpenPartialHomeomorph.source
      · rw [Manifold.extendChartById, if_pos hy]
        exact (B'.ball i).chart.symm.toOpenPartialHomeomorph.left_inv hy
      · rw [Manifold.extendChartById, if_neg hy]
        rfl
    have hsub : (B'.ball i).chart.symm.toOpenPartialHomeomorph.symm '' K ⊆
        (B'.ball i).chart '' V i := by
      rintro y ⟨k, hk, rfl⟩
      refine ⟨k, hKV hk, ?_⟩
      rfl
    have hfinal : ∀ x ∈ Metric.closedBall (0 : E₃) 2,
        J' 1 ((B.ball i).chart x) = (B'.ball i).chart x := by
      intro x hx
      have hover : (B.ball i).chart x ∈ (B'.ball i).chart.target :=
        himg_sub (hsrcV i x hx)
      rw [(hJ'form 1 ((B.ball i).chart x)).1,
        extendChartById_chartSymm_of_target (B'.ball i).toBallChart (J 1) hover, hJact x hx]
    exact ⟨J', _, hJ'c, hJ'i, hfix0, hsub, hJ'fix, hfinal⟩
  choose J' U hJ'c hJ'i hJ'0 hUsub hJ'fix hJ'1 using hman
  refine B.isotopic_of_supportFamily B' J' U hJ'c hJ'i hJ'0 ?_ hJ'fix ?_ hJ'1
  · intro i j hij
    exact (hdisjV i j hij).mono (hUsub i) (hUsub j)
  · intro i j hij x hx hxu
    exact Set.disjoint_left.mp ((hdisjV i j hij).mono_left (hres_sub i))
      ⟨x, hx, rfl⟩ (hUsub j hxu)

theorem disjoint_reserve_of_relativeSupportRegion (B B' : BallMarking M I) {V : I → Set E₃}
    (hV : relativeSupportRegion B B' V) {i j : I} (hij : i ≠ j) :
    Disjoint (B.reserve i) ((B'.ball j).chart '' V j) := by
  obtain ⟨-, -, -, hsrcV, hdisjV⟩ := hV
  refine (hdisjV i j hij).mono_left ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hsrcV i x hx

theorem disjoint_reserve_of_relativeSupportRegion_self (B : BallMarking M I) {V : I → Set E₃}
    (hV : relativeSupportRegion B B V) {i j : I} (hij : i ≠ j) :
    Disjoint (B.reserve i) (B.reserve j) := by
  have hsrcV : ∀ k, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      (B.ball k).chart x ∈ (B.ball k).chart '' V k := fun k => hV.2.2.2.1 k
  refine (B.disjoint_reserve_of_relativeSupportRegion B hV hij).mono_right ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hsrcV j x hx

theorem exists_relativeSupportRegion_self_of_subsingleton (B : BallMarking M I) [Subsingleton I] :
    ∃ V : I → Set E₃, relativeSupportRegion B B V ∧ straightLineTube B B V := by
  refine ⟨fun i => (B.ball i).chart.source, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun i => (B.ball i).chart.open_source
  · exact fun _ => subset_rfl
  · exact fun i => (B.ball i).closedBall_subset_source
  · intro i x hx
    exact ⟨x, (B.ball i).closedBall_subset_source hx, rfl⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · intro i t ht
    have h0 : (0 : E₃) ∈ (B.ball i).chart.source :=
      (B.ball i).closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
    have hsymm : (B.ball i).chart.symm ((B.ball i).chart (0 : E₃)) = (0 : E₃) :=
      PartialDiffeomorph.symm_apply_apply (B.ball i).chart h0
    rw [hsymm]
    simpa using h0

theorem isotopic_self_of_subsingleton (B : BallMarking M I) [Subsingleton I] : B.Isotopic B := by
  obtain ⟨V, hV, htube⟩ := B.exists_relativeSupportRegion_self_of_subsingleton
  exact B.isotopic_of_relativeSupportRegion B hV htube B.orientationCompatible_self

theorem exists_relativeSupportRegion_of_disjoint_support_regions (B B' : BallMarking M I)
    (W : I → Set M.Carrier) (hopen : ∀ i, IsOpen (W i))
    (htarget : ∀ i, W i ⊆ (B'.ball i).chart.target)
    (hsrc : ∀ i, (B.ball i).chart '' Metric.closedBall (0 : E₃) 2 ⊆ W i)
    (htgt : ∀ i, (B'.ball i).chart '' Metric.closedBall (0 : E₃) 2 ⊆ W i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) :
    ∃ V : I → Set E₃, relativeSupportRegion B B' V := by
  have himg : ∀ i, (B'.ball i).chart ''
      ((B'.ball i).chart.symm.toOpenPartialHomeomorph '' W i) = W i := by
    intro i
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      rw [show (B'.ball i).chart
          ((B'.ball i).chart.symm.toOpenPartialHomeomorph w) = w from
        PartialDiffeomorph.apply_symm_apply (B'.ball i).chart (htarget i hw)]
      exact hw
    · intro hy
      exact ⟨(B'.ball i).chart.symm.toOpenPartialHomeomorph y, ⟨y, hy, rfl⟩,
        PartialDiffeomorph.apply_symm_apply (B'.ball i).chart (htarget i hy)⟩
  refine ⟨fun i => (B'.ball i).chart.symm.toOpenPartialHomeomorph '' W i,
    fun i => (B'.ball i).chart.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (hopen i) (htarget i), ?_, ?_, ?_, ?_⟩
  · intro i y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact (B'.ball i).chart.toPartialEquiv.map_target (htarget i hw)
  · intro i x hx
    exact ⟨(B'.ball i).chart x, htgt i ⟨x, hx, rfl⟩,
      PartialDiffeomorph.symm_apply_apply (B'.ball i).chart
        ((B'.ball i).closedBall_subset_source hx)⟩
  · intro i x hx
    rw [himg i]
    exact hsrc i ⟨x, hx, rfl⟩
  · intro i j hij
    rw [himg i, himg j]
    exact hdisj i j hij

theorem exists_relativeSupportRegion_of_isEmpty (B B' : BallMarking M I) [IsEmpty I] :
    ∃ V : I → Set E₃, relativeSupportRegion B B' V ∧ straightLineTube B B' V := by
  refine ⟨fun i => (B'.ball i).chart.source, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun i => (B'.ball i).chart.open_source
  · exact fun _ => subset_rfl
  · exact fun i => (B'.ball i).closedBall_subset_source
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i
  · intro i
    exact isEmptyElim i

theorem isotopic_of_isEmpty (B B' : BallMarking M I) [IsEmpty I] : B.Isotopic B' := by
  obtain ⟨V, hV, htube⟩ := B.exists_relativeSupportRegion_of_isEmpty B'
  exact B.isotopic_of_relativeSupportRegion B' hV htube fun i => isEmptyElim i

end BallMarking

private theorem preservesOrientation_of_eqOn_closedBall_chart
    {M : ConnectedClosedOrientedManifold.{u} 3}
    {c c' : OrientedBallChart M.toClosedOrientedManifold}
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
    (hΦ : ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      Φ (c.toBallChart.chart x) = c'.toBallChart.chart x) :
    Φ.preservesOrientation M.orientation M.orientation := by
  have h0c : (0 : E₃) ∈ c.toBallChart.chart.source :=
    c.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have h0c' : (0 : E₃) ∈ c'.toBallChart.chart.source :=
    c'.toBallChart.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hEq : (fun x : E₃ => Φ (c.toBallChart.chart x)) =ᶠ[𝓝 (0 : E₃)]
      (fun x : E₃ => c'.toBallChart.chart x) :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds (0 : E₃) (by norm_num)) hΦ
  have hchain : mfderiv (𝓡 3) (𝓡 3) (fun x : E₃ => Φ (c.toBallChart.chart x)) 0
      = mfderiv (𝓡 3) (𝓡 3) (⇑Φ) (c.toBallChart.chart 0)
        ∘L mfderiv (𝓡 3) (𝓡 3) (fun x : E₃ => c.toBallChart.chart x) 0 :=
    mfderiv_comp (x := (0 : E₃)) (f := fun x : E₃ => c.toBallChart.chart x) (g := ⇑Φ)
      (Φ.mdifferentiable (by simp) _)
      (PartialDiffeomorph.mdifferentiableAt c.toBallChart.chart (by simp) h0c)
  have hkey : mfderiv (𝓡 3) (𝓡 3) (⇑Φ) (c.toBallChart.chart 0)
      ∘L mfderiv (𝓡 3) (𝓡 3) (fun x : E₃ => c.toBallChart.chart x) 0
      = mfderiv (𝓡 3) (𝓡 3) (fun x : E₃ => c'.toBallChart.chart x) 0 := by
    rw [← hchain, Filter.EventuallyEq.mfderiv_eq hEq]
  have h3 : (OrientationAssembly.chartTangentEquiv c h0c).toLinearEquiv.trans
      ((Φ.mfderivToContinuousLinearEquiv (by simp) (c.toBallChart.chart 0)).toLinearEquiv)
      = (OrientationAssembly.chartTangentEquiv c' h0c').toLinearEquiv := by
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    exact DFunLike.congr_fun hkey v
  refine Diffeomorph.preservesOrientation_of_eq_at Φ M.orientation M.orientation
    (c.toBallChart.chart 0) ?_
  rw [hΦ 0 (Metric.mem_closedBall_self (by norm_num))]
  erw [OrientationAssembly.orientation_eq_map_chartTangentEquiv c h0c,
    OrientationAssembly.orientation_map_map_trans
      (OrientationAssembly.chartTangentEquiv c h0c).toLinearEquiv
      ((Φ.mfderivToContinuousLinearEquiv (by simp) (c.toBallChart.chart 0)).toLinearEquiv)
      (OrientationAssembly.stdOrientation 0),
    h3]
  exact (OrientationAssembly.orientation_eq_map_chartTangentEquiv c' h0c').symm

theorem selfTransport_of_G_ball (h : G_ball.{u}) : SelfTransport.{u} := by
  refine fun {M} c c' => ?_
  let B : BallMarking M.toClosedOrientedManifold (ULift.{u} PUnit) :=
    { ball := fun _ => c
      reserve_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij }
  let B' : BallMarking M.toClosedOrientedManifold (ULift.{u} PUnit) :=
    { ball := fun _ => c'
      reserve_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij }
  obtain ⟨Φ, hΦ⟩ := (h M.toClosedOrientedManifold (ULift.{u} PUnit) B B').toTransport
  exact ⟨Φ, preservesOrientation_of_eqOn_closedBall_chart Φ fun x hx => hΦ ⟨PUnit.unit⟩ x hx,
    fun x hx => hΦ ⟨PUnit.unit⟩ x hx⟩

theorem G_ball_of_relativeSupportRegion
    (h : ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u) [Fintype I]
      (B B' : BallMarking M I),
      (∃ V : I → Set E₃, BallMarking.relativeSupportRegion B B' V ∧
        BallMarking.straightLineTube B B' V) ∧
      BallMarking.orientationCompatible B B') :
    G_ball.{u} := by
  intro M _ I _ B B'
  obtain ⟨⟨V, hV, htube⟩, hori⟩ := h M I B B'
  exact B.isotopic_of_relativeSupportRegion B' hV htube hori

end DifferentialGeometry.Topology
