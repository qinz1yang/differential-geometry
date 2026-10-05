import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimSurfaceFactorProducer

/-!
The orientation of a slim surface factor is exposed on its actual splitting product map.
The ordered line direction followed by the surface basis agrees with the model orientation.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Manifold GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P2" => Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ

local instance slimFactorOrientationFinrank : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [instMetricM : MetricSpace M] [instChartedM : ChartedSpace E3 M]
  [instManifoldM : IsManifold 𝓘(ℝ, E3) ∞ M] [instSigmaM : SigmaCompactSpace M]
  [instBundleM : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [instRiemannianM : IsRiemannianManifold 𝓘(ℝ, E3) M] [instCompleteM : CompleteSpace M]
  [instContinuousM : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
  {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [instMetricY : MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
  {c : SlimChart g hEnorm Δ σ α} {K : ℕ}


def SlimSurfaceFactor.zeroCarrier (P : SlimProductModel c K) (Q : SlimSurfaceFactor P)
    (s : Q.S) : {x : P.N // (P.e x).fst = 0} :=
  ((splittingProductEquiv P.e).symm (P.e.symm (toLp 2 (0, Q.ψ s)))).2

theorem SlimSurfaceFactor.zeroCarrier_val (P : SlimProductModel c K) (Q : SlimSurfaceFactor P)
    (s : Q.S) : (Q.zeroCarrier P s).val = P.e.symm (toLp 2 (0, Q.ψ s)) := by
  rw [zeroCarrier, splittingProductEquiv_symm_val, IsometryEquiv.apply_symm_apply]
  rfl

theorem SlimSurfaceFactor.zeroCarrier_contMDiff {P : SlimProductModel c K}
    (Q : SlimSurfaceFactor P) (hK : 4 ≤ K) :
    letI _slimZeroCharts := splittingFactorChartedSpace P.G
      (by exact_mod_cast (show 2 ≤ K - 2 by omega))
      P.enorm P.e
    ContMDiff (𝓡 2) 𝓘(ℝ, P2) 1 (Q.zeroCarrier P) := by
  let hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 2 ≤ K - 2 by omega)
  let slimZeroCharts := splittingFactorChartedSpace P.G hk P.enorm P.e
  have h1K : (1 : ℕ∞ω) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have h1r : (1 : ℕ∞ω) ≤ (((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) := by
    exact_mod_cast (show 1 ≤ K - 2 by omega)
  exact ((contMDiff_splittingProductEquiv_symm P.G hk P.enorm P.e).of_le h1r).snd.comp
    ((Q.product_contMDiff.of_le h1K).comp (contMDiff_const.prodMk contMDiff_id))

theorem SlimSurfaceFactor.zeroCarrier_mfderiv_injective {P : SlimProductModel c K}
    (Q : SlimSurfaceFactor P) (hK : 4 ≤ K) :
    letI _slimZeroCharts := splittingFactorChartedSpace P.G
      (by exact_mod_cast (show 2 ≤ K - 2 by omega))
      P.enorm P.e
    ∀ s : Q.S, Injective (mfderiv (𝓡 2) 𝓘(ℝ, P2) (Q.zeroCarrier P) s) := by
  let hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 2 ≤ K - 2 by omega)
  let slimZeroCharts := splittingFactorChartedSpace P.G hk P.enorm P.e
  let slimZeroManifold := splittingFactor_isManifold_one P.G hk P.enorm P.e
  have h1K : (1 : ℕ∞ω) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hval := (contMDiff_splittingFactor_val P.G hk P.enorm P.e).of_le
    (show (1 : ℕ∞ω) ≤ (((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2 by
      rw [withTop_natCast_add_two]
      exact_mod_cast (show 1 ≤ K - 2 + 2 by omega))
  have hi : ContMDiff 𝓘(ℝ, P2) (𝓡 2) 1
      (fun z : {x : P.N // (P.e x).fst = 0} => Q.ψ.symm (P.e z.val).snd) :=
    (Q.product_symm_contMDiff.of_le h1K).snd.comp hval
  have hleft : (fun z : {x : P.N // (P.e x).fst = 0} => Q.ψ.symm (P.e z.val).snd) ∘
      Q.zeroCarrier P = id := by
    funext s
    simp only [comp_apply, Q.zeroCarrier_val P, IsometryEquiv.apply_symm_apply]
    exact Q.ψ.symm_apply_apply s
  intro s v w hvw
  have hd := mfderiv_comp s (hi.mdifferentiableAt one_ne_zero (x := Q.zeroCarrier P s))
    ((Q.zeroCarrier_contMDiff hK).mdifferentiableAt one_ne_zero (x := s))
  rw [hleft, mfderiv_id] at hd
  exact (congrArg (fun A => A v) hd).trans
    ((congrArg (fun u => mfderiv 𝓘(ℝ, P2) (𝓡 2)
      (fun z : {x : P.N // (P.e x).fst = 0} => Q.ψ.symm (P.e z.val).snd)
      (Q.zeroCarrier P s) u) hvw).trans (congrArg (fun A => A w) hd).symm)

theorem SlimSurfaceFactor.product_eq_carrier {P : SlimProductModel c K}
    (Q : SlimSurfaceFactor P) (hK : 4 ≤ K) :
    letI _slimZeroCharts := splittingFactorChartedSpace P.G
      (by exact_mod_cast (show 2 ≤ K - 2 by omega)) P.enorm P.e
    letI _slimZeroManifold := splittingFactor_isManifold_one P.G
      (by exact_mod_cast (show 2 ≤ K - 2 by omega)) P.enorm P.e
    (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) =
      fun q : ℝ × Q.S => splittingProductDiffeomorph P.G
        (by exact_mod_cast (show 2 ≤ K - 2 by omega)) P.enorm P.e
          (q.1, Q.zeroCarrier P q.2) := by
  let hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 2 ≤ K - 2 by omega)
  let slimZeroCharts := splittingFactorChartedSpace P.G hk P.enorm P.e
  let slimZeroManifold := splittingFactor_isManifold_one P.G hk P.enorm P.e
  funext q
  rw [splittingProductDiffeomorph_apply]
  change _ = P.e.symm (toLp 2 (q.1, (P.e (Q.zeroCarrier P q.2).val).snd))
  rw [Q.zeroCarrier_val, IsometryEquiv.apply_symm_apply]
  rfl

theorem SlimSurfaceFactor.product_mfderiv_carrier {P : SlimProductModel c K}
    (Q : SlimSurfaceFactor P) (hK : 4 ≤ K) (s : Q.S) (v : ℝ × E2) :
    letI _slimZeroCharts := splittingFactorChartedSpace P.G
      (by exact_mod_cast (show 2 ≤ K - 2 by omega)) P.enorm P.e
    letI _slimZeroManifold := splittingFactor_isManifold_one P.G
      (by exact_mod_cast (show 2 ≤ K - 2 by omega)) P.enorm P.e
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
        (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P2)) (𝓡 3)
        (splittingProductDiffeomorph P.G
          (by exact_mod_cast (show 2 ≤ K - 2 by omega)) P.enorm P.e)
        (0, Q.zeroCarrier P s)
        (v.1, mfderiv (𝓡 2) 𝓘(ℝ, P2) (Q.zeroCarrier P) s v.2) := by
  let hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 2 ≤ K - 2 by omega)
  let slimZeroCharts := splittingFactorChartedSpace P.G hk P.enorm P.e
  let slimZeroManifold := splittingFactor_isManifold_one P.G hk P.enorm P.e
  let Ψ := splittingProductDiffeomorph P.G hk P.enorm P.e
  have hf := Q.product_eq_carrier hK
  have hd := mfderiv_comp_prodMap_id_apply Ψ (Q.zeroCarrier P) (0, s)
    (Ψ.contMDiff.mdifferentiableAt (by simp) (x := (0, Q.zeroCarrier P s)))
    ((Q.zeroCarrier_contMDiff hK).mdifferentiableAt one_ne_zero (x := s)) v
  exact (congrArg (fun f => mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) f (0, s) v) hf).trans hd

theorem SlimSurfaceFactor.product_frame {P : SlimProductModel c K}
    (Q : SlimSurfaceFactor P) (hK : 4 ≤ K) (s : Q.S) :
    ambientSplitFrame (𝓡 3) (𝓡 2) (Subtype.val ∘ Q.zeroCarrier P)
        (fun s => splittingFrame P.G P.e (Q.zeroCarrier P s).val) s =
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
        (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) := by
  let hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 2 ≤ K - 2 by omega)
  let slimZeroCharts := splittingFactorChartedSpace P.G hk P.enorm P.e
  let slimZeroManifold := splittingFactor_isManifold_one P.G hk P.enorm P.e
  rw [splittingCarrierFrame_eq_mfderiv_product P.G hk P.enorm P.e
    (Q.zeroCarrier P) (Q.zeroCarrier_contMDiff hK) s]
  exact ContinuousLinearMap.ext fun v => (Q.product_mfderiv_carrier hK s v).symm

private theorem slimOrientationCast_roundtrip {S : Type*} [instTopS : TopologicalSpace S]
    [instChartedS : ChartedSpace E2 S] [instManifoldS : IsManifold (𝓡 2) ∞ S]
    {n m : ℕ} (h : n = m) (O : ManifoldOrientation (𝓡 2) S n) :
    manifoldOrientationCast h.symm (manifoldOrientationCast h O) = O := by
  cases h
  rfl

theorem exists_slimSurfaceFactor_orientation (hK : 4 ≤ K) (P : SlimProductModel c K)
    (oN : ManifoldOrientation (𝓡 3) P.N 3) :
    ∃ Q : SlimSurfaceFactor P, ∃ L : (s : Q.S) → (ℝ × E2) ≃L[ℝ] E3,
      (∀ (s : Q.S) (v : ℝ × E2), L s v =
        mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
          (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v) ∧
      (∀ (s : Q.S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2),
        b.orientation = (manifoldOrientationCast (by simp) Q.orientation).orientation s ↔
          (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
            (L s).toLinearEquiv).orientation =
            (manifoldOrientationCast (by simp) oN).orientation
              (P.e.symm (toLp 2 (0, Q.ψ s)))) := by
  obtain ⟨Q⟩ := nonempty_slimSurfaceFactor hK P oN
  let hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by
    exact_mod_cast (show 2 ≤ K - 2 by omega)
  let slimZeroCharts := splittingFactorChartedSpace P.G hk P.enorm P.e
  let slimZeroManifold := splittingFactor_isManifold_one P.G hk P.enorm P.e
  let φ := Q.zeroCarrier P
  have hφ : ContMDiff (𝓡 2) 𝓘(ℝ, P2) 1 φ := Q.zeroCarrier_contMDiff hK
  have hinj : ∀ s, Injective (mfderiv (𝓡 2) 𝓘(ℝ, P2) φ s) :=
    Q.zeroCarrier_mfderiv_injective hK
  let oM := smoothOrientationOfManifoldOrientation (𝓡 3)
    (manifoldOrientationCast (by simp) oN)
  let oS := splittingCarrierOrientation P.G hk P.enorm P.e
    (Basis.singleton (Fin 1) ℝ) lineSurfaceIndex φ hφ hinj oM
  obtain ⟨O, hO⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) oS
  let Q' : SlimSurfaceFactor P := { Q with orientation := manifoldOrientationCast (by simp) O }
  let L := ambientSplitFrameEquiv (𝓡 3) (𝓡 2) (Subtype.val ∘ φ)
    (fun s => splittingFrame P.G P.e (φ s).val)
    (bijective_splittingFrame_carrier P.G hk P.enorm P.e
      (Basis.singleton (Fin 1) ℝ) lineSurfaceIndex φ hφ hinj)
  refine ⟨Q', L, ?_, ?_⟩
  · intro s v
    exact congrArg (fun A => A v) (Q.product_frame hK s)
  · intro s b
    have hcast : (manifoldOrientationCast (by simp) Q'.orientation).orientation s = oS.val s := by
      change (manifoldOrientationCast (show 2 = finrank ℝ E2 by simp)
        (manifoldOrientationCast (show finrank ℝ E2 = 2 by simp) O)).orientation s = oS.val s
      have hdim : finrank ℝ E2 = 2 := by simp
      have hround : manifoldOrientationCast hdim.symm
          (manifoldOrientationCast hdim O) = O :=
        slimOrientationCast_roundtrip hdim O
      rw [hround]
      exact congrFun hO s
    rw [hcast]
    have hiff := splittingCarrierOrientation_eq_iff
      (g := P.G) (hr := hk) (hnorm := P.enorm) (e := P.e)
      (bF := Basis.singleton (Fin 1) ℝ) (σ := lineSurfaceIndex)
      (φ := φ) (hφ := hφ) (hinj := hinj) (oM := oM) (s := s) (b := b)
    have hvalue : (φ s).val = P.e.symm (toLp 2 (0, Q'.ψ s)) :=
      Q.zeroCarrier_val P s
    change b.orientation = oS.val s ↔
      (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
        (L s).toLinearEquiv).orientation = oM.val (P.e.symm (toLp 2 (0, Q'.ψ s)))
    rw [← hvalue]
    exact hiff

end DifferentialGeometry.Geometry.Collapse
