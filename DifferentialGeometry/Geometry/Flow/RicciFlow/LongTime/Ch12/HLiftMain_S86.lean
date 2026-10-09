import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLift_S86

/-!
# CH12-S86 G1: radial path lifting `hlift_S86`
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic Set Manifold
open DifferentialGeometry.CheegerGromovCompactness TopologicalSpace
open DifferentialGeometry.Topology.Manifold Bundle
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Radial path lifting** (`[T2Space N]` is essential, see `[FROZEN v2] CH12-S76`). -/
theorem hlift_S86 (H H' : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [T2Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N]
    (gN : SmoothRiemannianMetric (𝓡 3) N) (U : Opens H.Carrier) (U' : Opens H'.Carrier)
    (f : H.Carrier → N) (φ : H'.Carrier → N) (R : ℝ) (hR : 0 < R)
    (hbU : riemannianBallOf H.metric H.basepoint (2 * R + 2) ⊆ U)
    (hbU' : riemannianBallOf H'.metric H'.basepoint (8 * R + 8) ⊆ U')
    (hfU : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hfemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (hφU' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U')
    (hφemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U' => φ x))
    (hbase : f H.basepoint = φ H'.basepoint)
    (hck : ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R + 2),
      ckErr_O19 H gN 1 f 0 p < 1 / 8)
    (hck' : ∀ q ∈ riemannianBallOf H'.metric H'.basepoint (8 * R + 8),
      ckErr_O19 H' gN 1 φ 0 q < 1 / 8) :
    ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
      ∃ q ∈ riemannianBallOf H'.metric H'.basepoint (8 * R + 8), φ q = f p := by
  intro p hp
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  let B : Opens H.Carrier :=
    ⟨riemannianBallOf H.metric H.basepoint (2 * R + 2), isOpen_riemannianBallOf _ _ _⟩
  let B' : Opens H'.Carrier :=
    ⟨riemannianBallOf H'.metric H'.basepoint (8 * R + 8), isOpen_riemannianBallOf _ _ _⟩
  have hBU : (B : Set H.Carrier) ⊆ U := hbU
  have hB'U' : (B' : Set H'.Carrier) ⊆ U' := hbU'
  have hfB : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f B := hfU.mono hBU
  have hφB' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ B' := hφU'.mono hB'U'
  have hinjfB : ∀ y ∈ B, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) := fun y hy =>
    injective_mfderiv_of_embedding_S86 f U hfU hfemb y (hBU hy)
  have hinjφB' : ∀ y ∈ B', Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) := fun y hy =>
    injective_mfderiv_of_embedding_S86 φ U' hφU' hφemb y (hB'U' hy)
  have spf := speed_comparison_S86 H gN f B hfB hinjfB hck
  have spφ := speed_comparison_S86 H' gN φ B' hφB' hinjφB' hck'
  set F : B' → N := fun z => φ z with hFdef
  have hFsm : ContMDiff (𝓡 3) (𝓡 3) ∞ F := contMDiff_restrict_C4 φ B' hφB'
  have hFinj : ∀ x : B', Function.Injective (mfderiv (𝓡 3) (𝓡 3) F x) :=
    fun z v w hvw => hinjφB' z z.2
      ((mfderiv_comp_val_C4 φ B' hφB' z v).symm.trans
        (hvw.trans (mfderiv_comp_val_C4 φ B' hφB' z w)))
  have hFld : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ F :=
    isLocalDiffeomorph_of_injective_mfderiv F hFsm hFinj rfl
  let rbH : RiemannianBundle (fun x : H.Carrier => TangentSpace (𝓡 3) x) :=
    ⟨H.metric.toRiemannianMetric⟩
  let rbN : RiemannianBundle (fun x : N => TangentSpace (𝓡 3) x) := ⟨gN.toRiemannianMetric⟩
  let rbX : RiemannianBundle (fun x : B' => TangentSpace (𝓡 3) x) :=
    ⟨(H'.metric.restrictOpen B').toRiemannianMetric⟩
  have hnH : ∀ (x : H.Carrier) (v : TangentSpace (𝓡 3) x),
      ‖v‖ₑ = ENNReal.ofReal √(H.metric.inner x v v) := fun x v =>
    Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm H.metric x v
  have hnN : ∀ (x : N) (v : TangentSpace (𝓡 3) x),
      ‖v‖ₑ = ENNReal.ofReal √(gN.inner x v v) := fun x v =>
    Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm gN x v
  have hnX : ∀ (x : B') (v : TangentSpace (𝓡 3) x),
      ‖v‖ₑ = ENNReal.ofReal √((H'.metric.restrictOpen B').inner x v v) := fun x v =>
    Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (H'.metric.restrictOpen B') x v
  have hspX : ∀ (x : B') (v : TangentSpace (𝓡 3) x),
      (H'.metric.restrictOpen B').inner x v v ≤
        2 * gN.inner (F x) (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x v) := by
    intro x v
    have h1 := (spφ x x.2 v).2
    have e := mfderiv_comp_val_C4 φ B' hφB' x v
    change _ ≤ 2 * gN.inner (φ x) (mfderiv (𝓡 3) (𝓡 3) (fun z : B' => φ z) x v)
      (mfderiv (𝓡 3) (𝓡 3) (fun z : B' => φ z) x v)
    rw [e]
    exact h1
  -- radial path
  have hpd : Manifold.riemannianEDist (𝓡 3) H.basepoint p < ENNReal.ofReal R := hp
  obtain ⟨γ0, hγ00, hγ01, hγ0, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hpd
  have hγB : ∀ s ∈ Icc (0 : ℝ) 1, γ0 s ∈ B := by
    intro s hs
    have h1 : Manifold.riemannianEDist (𝓡 3) H.basepoint (γ0 s) ≤ pathELength (𝓡 3) γ0 0 s :=
      Manifold.riemannianEDist_le_pathELength (hγ0.mono (Icc_subset_Icc le_rfl hs.2)) hγ00
        rfl hs.1
    have h2 : pathELength (𝓡 3) γ0 0 s ≤ pathELength (𝓡 3) γ0 0 1 :=
      Manifold.pathELength_mono le_rfl hs.2
    exact (h1.trans (h2.trans hlen.le)).trans_lt (ENNReal.ofReal_lt_ofReal_iff'.mpr
      ⟨by linarith, by linarith⟩) |>.trans_le le_rfl
  have hγsm : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ γ0) (Icc 0 1) :=
    (hfB.of_le (by simp)).comp hγ0 (fun s hs => hγB s hs)
  have hz : F ⟨H'.basepoint, by
      change riemannianEDistOf H'.metric H'.basepoint H'.basepoint < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by linarith)⟩ = (f ∘ γ0) 0 := by
    change φ H'.basepoint = f (γ0 0)
    rw [hγ00, hbase]
  have hzmem : H'.basepoint ∈ B' := by
    change riemannianEDistOf H'.metric H'.basepoint H'.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  let z : B' := ⟨H'.basepoint, hzmem⟩
  let K : Set B' :=
    {x | riemannianEDistOf H'.metric H'.basepoint (x : H'.Carrier) ≤ ENNReal.ofReal (4 * R + 4)}
  have hK : IsCompact K := by
    have hC := RiemannianMetricComplete.closedEBall_isCompact H'.complete H'.basepoint (4 * R + 4)
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr ?_
    convert hC using 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, lt_of_le_of_lt hy (ENNReal.ofReal_lt_ofReal_iff'.mpr
        ⟨by linarith, by linarith⟩)⟩, hy, rfl⟩
  have hγd : ∀ᵐ s ∂MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) γ0 s :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
      ((hγ0 s (Ioo_subset_Icc_self hs)).mdifferentiableWithinAt (by simp)).mdifferentiableAt
        (Icc_mem_nhds hs.1 hs.2)
  have hfd : ∀ᵐ s ∂MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt (𝓡 3) (𝓡 3) f (γ0 s) :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
      (hfB.contMDiffAt (B.isOpen.mem_nhds (hγB s (Ioo_subset_Icc_self hs)))).mdifferentiableAt hinf
  have hnf : ∀ᵐ s ∂MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1),
      ‖mfderiv (𝓡 3) (𝓡 3) f (γ0 s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ0 s 1)‖ₑ ≤
        ((2 : NNReal) : ENNReal) * ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ0 s 1‖ₑ :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun s hs => by
      rw [hnN, hnH]
      exact ofReal_sqrt_le_two_mul_S86 _ _ (spf _ (hγB s (Ioo_subset_Icc_self hs)) _).1
  have hlenγ : pathELength (𝓡 3) (f ∘ γ0) 0 1 ≤ ((2 : NNReal) : ENNReal) * pathELength (𝓡 3) γ0 0 1 :=
    pathELength_comp_le_of_enorm_mfderiv_le f 2 hγd hfd hnf
  obtain ⟨η, hη⟩ := exists_isPathLiftOn_of_isCompact (F := F) hFld.isLocalHomeomorph zero_le_one
    hγsm.continuousOn hz hK (by
      intro t ht η hη
      have hγt : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ γ0) (Icc 0 t) :=
        hγsm.mono (Icc_subset_Icc le_rfl ht.2)
      have hη1 := isPathLiftOn_contMDiffOn_C1_S86 hFld hγt hη
      have hηd : ∀ᵐ s ∂MeasureTheory.volume.restrict (Ioo 0 t),
          MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) η s :=
        (MeasureTheory.ae_restrict_mem measurableSet_Ioo).mono fun s hs =>
          ((hη1 s (Ioo_subset_Icc_self hs)).mdifferentiableWithinAt (by simp)).mdifferentiableAt
            (Icc_mem_nhds hs.1 hs.2)
      have hlenη : pathELength (𝓡 3) η 0 t ≤
          ((2 : NNReal) : ENNReal) * pathELength (𝓡 3) (f ∘ γ0) 0 1 := by
        calc pathELength (𝓡 3) η 0 t
            ≤ ((2 : NNReal) : ENNReal) * pathELength (𝓡 3) (F ∘ η) 0 t :=
              pathELength_le_comp_S86 F 2 hηd
                (Filter.Eventually.of_forall fun s => (hFsm (η s)).mdifferentiableAt hinf)
                (Filter.Eventually.of_forall fun s => by
                  rw [hnX, hnN]
                  exact ofReal_sqrt_le_two_mul_S86 _ _ (hspX _ _))
          _ = ((2 : NNReal) : ENNReal) * pathELength (𝓡 3) (f ∘ γ0) 0 t := by
              exact congrArg (fun L => ((2 : NNReal) : ENNReal) * L)
                (pathELength_congr (fun s hs => hη.2.2 s hs))
          _ ≤ ((2 : NNReal) : ENNReal) * pathELength (𝓡 3) (f ∘ γ0) 0 1 := by
              gcongr
              exact ht.2
      change riemannianEDistOf H'.metric H'.basepoint (η t) ≤ ENNReal.ofReal (4 * R + 4)
      calc riemannianEDistOf H'.metric H'.basepoint (η t)
          ≤ riemannianEDistOf (H'.metric.restrictOpen B') z (η t) :=
            riemannianEDistOf_le_restrictOpen H'.metric B' z (η t)
        _ ≤ pathELength (𝓡 3) η 0 t :=
            Manifold.riemannianEDist_le_pathELength hη1 hη.2.1 rfl ht.1
        _ ≤ ((2 : NNReal) : ENNReal) * (((2 : NNReal) : ENNReal) * pathELength (𝓡 3) γ0 0 1) :=
            hlenη.trans (by gcongr)
        _ ≤ ((2 : NNReal) : ENNReal) * (((2 : NNReal) : ENNReal) * ENNReal.ofReal R) := by
            gcongr
        _ = ENNReal.ofReal (4 * R) := by
            rw [show 4 * R = 2 * (2 * R) by ring, ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num)]
            simp
        _ ≤ ENNReal.ofReal (4 * R + 4) := ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨(η 1 : H'.Carrier), (η 1).2, ?_⟩
  have h1 := hη.2.2 1 ⟨zero_le_one, le_rfl⟩
  change φ (η 1) = f (γ0 1) at h1
  rw [hγ01] at h1
  exact h1

end GC.LongTime.Ch12
