import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity

set_option autoImplicit false

noncomputable section

open Set Filter Matrix
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong (covDerivAlong)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
theorem lVelocity_affine_eq_mfderiv {β : P × ℝ → M} {V : Set P} {K : Set ℝ} (hV : IsOpen V)
    (hK : IsOpen K) (hβ : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (V ×ˢ K)) {Z₀ : P}
    (hZ₀ : Z₀ ∈ V) (B : P) {r : ℝ} (hr : r ∈ K) :
    (lVelocity (I := I) (fun u : ℝ => β (Z₀ + u • B, r)) 0 : E) =
      mfderiv 𝓘(ℝ, P) I (fun Z => β (Z, r)) Z₀ B := by
  have hβr : MDifferentiableAt 𝓘(ℝ, P) I (fun Z => β (Z, r)) Z₀ :=
    (((hβ (Z₀, r) ⟨hZ₀, hr⟩).contMDiffAt ((hV.prod hK).mem_nhds ⟨hZ₀, hr⟩)).comp Z₀
      (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)
  have hline : HasDerivAt (fun u : ℝ => Z₀ + u • B) ((1 : ℝ) • B) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add Z₀
  have hlineM : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, P) (fun u : ℝ => Z₀ + u • B) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((1 : ℝ) • B)) :=
    hasMFDerivAt_iff_hasFDerivAt.2 hline.hasFDerivAt
  have h0 : (fun u : ℝ => Z₀ + u • B) 0 = Z₀ := by simp
  have hcomp := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, P)) (I'' := I) (x := 0)
    hβr hlineM.mdifferentiableAt h0 (1 : ℝ)
  rw [hlineM.mfderiv] at hcomp
  refine hcomp.trans ?_
  congr 1
  change ((1 : ℝ →L[ℝ] ℝ).smulRight ((1 : ℝ) • B) : ℝ →L[ℝ] P) 1 = B
  simp

theorem isLRegularizedJacobi_mfderiv_of_contMDiffOn (S : SolutionOn (I := I) (M := M) D)
    (T : ℝ) {β : P × ℝ → M} {V : Set P} {K : Set ℝ} (hV : IsOpen V) (hK : IsOpen K)
    (hβ : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (V ×ˢ K))
    (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn S T (fun r => β (Z, r)) K) {Z₀ : P}
    (hZ₀ : Z₀ ∈ V) (B : P) :
    IsLRegularizedJacobi S T (fun r => β (Z₀, r))
      (fun r => mfderiv 𝓘(ℝ, P) I (fun Z => β (Z, r)) Z₀ B) K := by
  intro s hs
  let f : ℝ → ℝ → M := fun u r => β (Z₀ + u • B, r)
  have hparam : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × ℝ => (Z₀ + q.1 • B, q.2)) (0, s) :=
    ((contMDiff_const.add (contMDiff_fst.smul contMDiff_const)).prodMk contMDiff_snd).contMDiffAt
  have hβat : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) I ∞ β (Z₀ + (0 : ℝ) • B, s) := by
    rw [zero_smul, add_zero]
    exact (hβ (Z₀, s) ⟨hZ₀, hs⟩).contMDiffAt ((hV.prod hK).mem_nhds ⟨hZ₀, hs⟩)
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 3 (fun q : ℝ × ℝ => f q.1 q.2) (0, s) :=
    (hβat.comp (0, s) hparam).of_le (by
      change (↑(3 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hnear : ∀ᶠ u in 𝓝 (0 : ℝ), Z₀ + u • B ∈ V := by
    have hc : Continuous fun u : ℝ => Z₀ + u • B := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV.mem_nhds hZ₀)
  have hgeoNear : ∀ᶠ u in 𝓝 (0 : ℝ),
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (f u)
          (fun r => lVelocity (I := I) (f u) r) s =
        lRegularizedAccel S T s (f u s) (lVelocity (I := I) (f u) s) := by
    filter_upwards [hnear] with u hu
    exact (hgeo _ hu s hs).2.2.2
  have hraw := lRegularizedVar_jacobiAt (I := I) S T f s hf hgeoNear
  refine HasLRegularizedJacobiAt.congr_of_eqOn S T _ _ s K hK hs (fun r _ => ?_)
    (fun r hr => ?_) hraw
  · simp only [f, zero_smul, add_zero]
  · exact lVelocity_affine_eq_mfderiv hV hK hβ hZ₀ B hr

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Integral.Measure (paramGramMatrix paramDensity paramGramMatrix_apply)
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong (chartRepAt)

universe u

variable {H : ObservedHistory.{u}}

section Defs

variable {first last : Fin (H.eventCount + 1)} (hle : first ≤ last) (T v : ℝ)
  (p : (H.stage last).Carrier)

variable (H) in
open Classical in
def historyLCurveMap (Z₀ : H.historyLExpDomain hle T v p) (j : H.StageInterval first last)
    (s : ℝ) (Z : ThreeSpace) : (H.stage j.val).Carrier :=
  if hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
    H.historyLCurve hle T v p ⟨Z, hZ⟩ j s
  else H.historyLCurve hle T v p Z₀ j s

variable (H) in
def historyLJacobiField (Z₀ : H.historyLExpDomain hle T v p) (j : H.StageInterval first last)
    (i : Fin (Module.finrank ℝ ThreeSpace)) (s : ℝ) :
    TangentSpace ThreeModel (H.historyLCurveMap hle T v p Z₀ j s Z₀.1) :=
  mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (H.historyLCurveMap hle T v p Z₀ j s) Z₀.1
    (chartModelBasis ThreeSpace i)

variable (H) in
def historyLGram (Z₀ : H.historyLExpDomain hle T v p) (j : H.StageInterval first last) (s : ℝ) :
    Matrix (Fin (Module.finrank ℝ ThreeSpace)) (Fin (Module.finrank ℝ ThreeSpace)) ℝ :=
  paramGramMatrix (H.stageMetric j.val (T - s ^ 2)) (H.historyLCurveMap hle T v p Z₀ j s) Z₀.1

variable (H) in
def historyLJacobianDensity (Z₀ : H.historyLExpDomain hle T v p)
    (j : H.StageInterval first last) (s : ℝ) : ℝ :=
  paramDensity (H.stageMetric j.val (T - s ^ 2)) (H.historyLCurveMap hle T v p Z₀ j s) Z₀.1

variable (H) in
def historyLSourceDensity : ℝ :=
  Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ ThreeSpace) =>
    (H.stageMetric last T).inner p (chartModelBasis ThreeSpace i)
      (chartModelBasis ThreeSpace k)).det

variable (H) in
def historyReducedJacobian (Z₀ : H.historyLExpDomain hle T v p) : ℝ :=
  H.historyLJacobianDensity hle T v p Z₀ ⟨first, le_rfl, hle⟩ v / H.historyLSourceDensity T p *
    Real.exp (-H.historyLAction hle T v p Z₀ / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi))

end Defs

section Basic

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier} {Z₀ : H.historyLExpDomain hle T v p}

theorem historyLCurveMap_of_mem (j : H.StageInterval first last) (s : ℝ) {Z : ThreeSpace}
    (hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) :
    H.historyLCurveMap hle T v p Z₀ j s Z = H.historyLCurve hle T v p ⟨Z, hZ⟩ j s :=
  dite_eq_left hZ

theorem historyLCurveMap_self (j : H.StageInterval first last) (s : ℝ) :
    H.historyLCurveMap hle T v p Z₀ j s Z₀.1 = H.historyLCurve hle T v p Z₀ j s :=
  historyLCurveMap_of_mem j s Z₀.2

theorem historyLGram_apply (j : H.StageInterval first last) (s : ℝ)
    (i k : Fin (Module.finrank ℝ ThreeSpace)) :
    H.historyLGram hle T v p Z₀ j s i k =
      (H.stageMetric j.val (T - s ^ 2)).inner (H.historyLCurveMap hle T v p Z₀ j s Z₀.1)
        (H.historyLJacobiField hle T v p Z₀ j i s) (H.historyLJacobiField hle T v p Z₀ j k s) :=
  rfl

theorem historyLJacobianDensity_eq_sqrt_det (j : H.StageInterval first last) (s : ℝ) :
    H.historyLJacobianDensity hle T v p Z₀ j s = Real.sqrt (H.historyLGram hle T v p Z₀ j s).det :=
  rfl

theorem historyLJacobianDensity_nonneg (j : H.StageInterval first last) (s : ℝ) :
    0 ≤ H.historyLJacobianDensity hle T v p Z₀ j s :=
  Real.sqrt_nonneg _

theorem historyLSourceDensity_nonneg : 0 ≤ H.historyLSourceDensity T p :=
  Real.sqrt_nonneg _

theorem historyLSourceDensity_pos : 0 < H.historyLSourceDensity T p :=
  Real.sqrt_pos.2 (DifferentialGeometry.Geometry.Riemannian.Variation.curveGram_det_pos
    (I := ThreeModel) (H.stageMetric last T) (fun _ => p) (fun i _ => chartModelBasis ThreeSpace i)
    0 (chartModelBasis ThreeSpace).linearIndependent)

theorem historyLJacobianDensity_pos (j : H.StageInterval first last) (s : ℝ)
    (hli : LinearIndependent ℝ fun i => H.historyLJacobiField hle T v p Z₀ j i s) :
    0 < H.historyLJacobianDensity hle T v p Z₀ j s :=
  Real.sqrt_pos.2 (DifferentialGeometry.Geometry.Riemannian.Variation.curveGram_det_pos
    (I := ThreeModel) (H.stageMetric j.val (T - s ^ 2))
    (fun r => H.historyLCurveMap hle T v p Z₀ j r Z₀.1)
    (fun i r => H.historyLJacobiField hle T v p Z₀ j i r) s hli)

theorem historyReducedJacobian_nonneg : 0 ≤ H.historyReducedJacobian hle T v p Z₀ :=
  mul_nonneg (div_nonneg (historyLJacobianDensity_nonneg _ _) historyLSourceDensity_nonneg)
    (Real.exp_pos _).le

private theorem paramDensity_congr {X : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X]
    (g : SmoothRiemannianMetric ThreeModel X)
    {w : ThreeSpace} {f f' : ThreeSpace → X} (h : f =ᶠ[𝓝 w] f') :
    paramDensity g f w = paramDensity g f' w := by
  simp only [paramDensity, paramGramMatrix]
  rw [h.mfderiv_eq, h.eq_of_nhds]

private theorem paramGramMatrix_apply_of_eventuallyEq_comp {X Y : Type*} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] [TopologicalSpace Y]
    [ChartedSpace ThreeSpace Y] [IsManifold ThreeModel ∞ Y]
    (g : SmoothRiemannianMetric ThreeModel Y)
    (gX : SmoothRiemannianMetric ThreeModel X) {F : X → Y}
    (hF : IsLocalDiffeomorph ThreeModel ThreeModel ∞ F) (hg : gX = localPullMetric g F hF)
    {w : ThreeSpace} {Φ : ThreeSpace → Y} {Ψ : ThreeSpace → X} (h : Φ =ᶠ[𝓝 w] F ∘ Ψ)
    (hΨ : MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel Ψ w)
    (a b : Fin (Module.finrank ℝ ThreeSpace)) :
    paramGramMatrix g Φ w a b = gX.inner (Ψ w)
      (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel Ψ w (chartModelBasis ThreeSpace a))
      (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel Ψ w (chartModelBasis ThreeSpace b)) := by
  have hFd := (hF (Ψ w)).mdifferentiableAt (by simp)
  have hc (e : ThreeSpace) : (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (F ∘ Ψ) w e : ThreeSpace) =
      mfderiv ThreeModel ThreeModel F (Ψ w) (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel Ψ w e) :=
    mfderiv_comp_apply w hFd hΨ e
  have hΦ : paramGramMatrix g Φ w = paramGramMatrix g (F ∘ Ψ) w := by
    simp only [paramGramMatrix]
    rw [h.mfderiv_eq, h.eq_of_nhds]
  rw [hΦ]
  subst hg
  exact (congrArg₂ (fun x y : ThreeSpace => g.inner (F (Ψ w)) x y) (hc _) (hc _)).trans
    (localPullMetric_inner g F hF (Ψ w) _ _).symm

theorem paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (j : H.StageInterval first last)
    (s : ℝ) {f : ThreeSpace → (H.stage j.val).Carrier}
    (hf : f =ᶠ[𝓝 Z₀.1] H.historyLCurveMap hle T v p Z₀ j s) :
    paramDensity (H.stageMetric j.val (T - s ^ 2)) f Z₀.1 =
      H.historyLJacobianDensity hle T v p Z₀ j s :=
  paramDensity_congr _ hf

theorem paramDensity_historyLExp_eq_historyLJacobianDensity (hv : 0 < v)
    (hZ₀ : Z₀.1 ∈ H.historyLExpOpenDomain hle T v p) {f : ThreeSpace → (H.stage first).Carrier}
    (hf : ∀ Z (hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p),
      f Z = H.historyLExp hle T v p ⟨Z, hZ⟩) :
    paramDensity (H.stageMetric first (T - v ^ 2)) f Z₀.1 =
      H.historyLJacobianDensity hle T v p Z₀ ⟨first, le_rfl, hle⟩ v := by
  refine paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := Z₀)
    ⟨first, le_rfl, hle⟩ v ?_
  filter_upwards [(isOpen_historyLExpOpenDomain hv).mem_nhds hZ₀] with Z hZ
  have hd := historyLExpOpenDomain_subset_historyLExpDomain hZ
  rw [hf Z hd, historyLCurveMap_of_mem _ _ hd]
  rfl

variable {B : ℝ} (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) x)

include hfloor in
theorem ofReal_historyReducedJacobian_eq (hv : 0 < v)
    (hZ : Z₀.1 ∈ H.historyMinDomain hle T B v p) :
    ENNReal.ofReal (H.historyReducedJacobian hle T v p Z₀) =
      ENNReal.ofReal (H.historyLJacobianDensity hle T v p Z₀ ⟨first, le_rfl, hle⟩ v /
        H.historyLSourceDensity T p) *
        H.regularizedDensity first last hle T B v p (H.historyLExp hle T v p Z₀) := by
  rw [regularizedDensity_historyLExp_eq hfloor hv Z₀ hZ, historyReducedJacobian,
    ENNReal.ofReal_mul (div_nonneg (historyLJacobianDensity_nonneg _ _)
      historyLSourceDensity_nonneg)]

end Basic

section Window

variable {first last lo hi : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier} {Z₀ : H.historyLExpDomain hle T v p}
  {hlo : first ≤ lo} {hhi : hi ≤ last} {W : H.LWindow lo hi T} {V : Set ThreeSpace} {K : Set ℝ}
  {β : ThreeSpace × ℝ → W.X}
  (hV : IsOpen V) (hZ₀V : Z₀.1 ∈ V)
  (hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p)
  (hK : IsOpen K) (hKW : K ⊆ Ioo W.a W.b)
  (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
  (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K)
  (hrep : ∀ Z (hZ : Z ∈ V) (j : H.StageInterval lo hi),
    ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
      H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r)))

include hV hZ₀V hrep in
private theorem eventuallyEq_historyLCurveMap (j : H.StageInterval lo hi) {r : ℝ}
    (hr : r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    H.historyLCurveMap hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r
      =ᶠ[nhds (X := ThreeSpace) Z₀.1] (W.f j ∘ fun Z => β (Z, r)) := by
  filter_upwards [hV.mem_nhds hZ₀V] with Z hZ
  rw [historyLCurveMap_of_mem _ _ (hVdom Z hZ)]
  exact hrep Z hZ j r hr

include hV hK hβ in
private theorem mdifferentiableAt_family {z : ThreeSpace} (hz : z ∈ V) {r : ℝ} (hr : r ∈ K) :
    MDifferentiableAt 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, r)) z :=
  (((hβ (z, r) ⟨hz, hr⟩).contMDiffAt ((hV.prod hK).mem_nhds ⟨hz, hr⟩)).comp z
    (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt (by simp)

include hV hZ₀V hK hβ hrep in
theorem historyLJacobiField_eq_mfderiv (j : H.StageInterval lo hi)
    (i : Fin (Module.finrank ℝ ThreeSpace)) {r : ℝ}
    (hr : r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    (H.historyLJacobiField hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
        i r : ThreeSpace) =
      mfderiv ThreeModel ThreeModel (W.f j) (β (Z₀.1, r))
        (mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, r)) Z₀.1
          (chartModelBasis ThreeSpace i)) := by
  have hev := eventuallyEq_historyLCurveMap (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hrep j hr
  unfold historyLJacobiField
  rw [hev.mfderiv_eq]
  exact mfderiv_comp_apply _ ((W.localDiffeomorph j _).mdifferentiableAt (by simp))
    (mdifferentiableAt_family hV hK hβ hZ₀V hr.1) _

include hV hZ₀V hK hβ hgeo hrep in
theorem isLRegularizedJacobi_historyLJacobiField (j : H.StageInterval lo hi) {D' : RealTimeInterval}
    (S' : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D') {K' : Set ℝ}
    (hK' : IsOpen K')
    (hK'sub : K' ⊆
      K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
    (hS' : ∀ s ∈ K', S'.base.metric (T - s ^ 2) = H.stageMetric j.val (T - s ^ 2))
    (i : Fin (Module.finrank ℝ ThreeSpace)) :
    IsLRegularizedJacobi S' T (fun r => H.historyLCurveMap hle T v p Z₀
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r Z₀.1)
      (fun r => H.historyLJacobiField hle T v p Z₀
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ i r) K' := by
  have hJ := W.isLRegularizedJacobi_comp j S' hK' (hK'sub.trans inter_subset_right) hS'
    (fun s hs => isLRegularizedJacobi_mfderiv_of_contMDiffOn W.S T hV hK hβ hgeo hZ₀V
      (chartModelBasis ThreeSpace i) s (hK'sub hs).1)
  intro s hs
  refine HasLRegularizedJacobiAt.congr_of_eqOn S' T _ _ s K' hK' hs (fun r hr => ?_)
    (fun r hr => (historyLJacobiField_eq_mfderiv (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hK hβ
      hrep j i (hK'sub hr)).symm) (hJ s hs)
  exact (eventuallyEq_historyLCurveMap (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hrep j
    (hK'sub hr)).eq_of_nhds.symm

include hV hZ₀V hK hKW hβ hrep in
theorem historyLGram_eq_lGram (j : H.StageInterval lo hi) {τ : ℝ}
    (hτ : Real.sqrt τ ∈
      K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    H.historyLGram hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
        (Real.sqrt τ) =
      lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) τ := by
  have hs0 : 0 < Real.sqrt τ := W.nonneg.trans_lt (hKW hτ.1).1
  have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt (Real.sqrt_pos.1 hs0).le
  have hm := W.metric j (Real.sqrt τ) hτ.2
  rw [hsq] at hm
  have hev := eventuallyEq_historyLCurveMap (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hrep j hτ
  ext a b
  simp only [historyLGram, lGram, Matrix.of_apply]
  rw [hsq]
  exact paramGramMatrix_apply_of_eventuallyEq_comp _ _ (W.localDiffeomorph j) hm hev
    (mdifferentiableAt_family hV hK hβ hZ₀V hτ.1) a b

include hV hZ₀V hK hKW hβ hrep in
theorem historyLJacobianDensity_eq_lJacobianDensity (j : H.StageInterval lo hi) {τ : ℝ}
    (hτ : Real.sqrt τ ∈
      K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    H.historyLJacobianDensity hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
        (Real.sqrt τ) =
      lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) τ := by
  rw [historyLJacobianDensity_eq_sqrt_det, historyLGram_eq_lGram (hlo := hlo) (hhi := hhi) hV hZ₀V
    hVdom hK hKW hβ hrep j hτ]
  rfl

include hV hZ₀V hK hKW hβ hrep in
theorem historyLJacobianDensity_eq_lJacobianDensity_sq (j : H.StageInterval lo hi) {r : ℝ}
    (hr : r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    H.historyLJacobianDensity hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
        r =
      lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) (r ^ 2) := by
  have hr0 : 0 ≤ r := W.nonneg.trans (hKW hr.1).1.le
  have h := historyLJacobianDensity_eq_lJacobianDensity (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hK
    hKW hβ hrep j (τ := r ^ 2) (by rw [Real.sqrt_sq hr0]; exact hr)
  rwa [Real.sqrt_sq hr0] at h

include hV hK hKW hβ hgeo in
private theorem lGram_hypotheses {z : ThreeSpace} (hz : z ∈ V) {τ : ℝ} (hτ : Real.sqrt τ ∈ K) :
    T - τ ∈ W.D.regular ∧
      MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (fun q => β (z, Real.sqrt q)) τ ∧
      ∀ i : Fin (Module.finrank ℝ ThreeSpace), DifferentiableAt ℝ
        (chartRepAt (I := ThreeModel) (fun q => β (z, Real.sqrt q))
          (fun q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) z
            (chartModelBasis ThreeSpace i)) τ) τ := by
  have hs0 : 0 < Real.sqrt τ := W.nonneg.trans_lt (hKW hτ).1
  have hτ0 : 0 < τ := Real.sqrt_pos.1 hs0
  have hsqrt := Real.hasDerivAt_sqrt hτ0.ne'
  refine ⟨?_, ?_, fun i => ?_⟩
  · have h := W.regular (Real.sqrt τ) ⟨(hKW hτ).1.le, (hKW hτ).2.le⟩
    rwa [Real.sq_sqrt hτ0.le] at h
  · exact ((hgeo z hz (Real.sqrt τ) hτ).2.1).comp τ
      (mdifferentiableAt_iff_differentiableAt.2 hsqrt.differentiableAt)
  · have hj := isLRegularizedJacobi_mfderiv_of_contMDiffOn W.S T hV hK hβ hgeo hz
      (chartModelBasis ThreeSpace i) (Real.sqrt τ) hτ
    exact hj.2.1.comp τ hsqrt.differentiableAt

include hV hZ₀V hK hKW hβ hgeo hrep in
theorem hasDerivAt_historyLJacobianDensity (j : H.StageInterval lo hi) {τ : ℝ}
    (hτ : Real.sqrt τ ∈
      K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val))
    (hpos : 0 < (lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) τ).det) :
    HasDerivAt (fun τ' => H.historyLJacobianDensity hle T v p Z₀
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ'))
      ((1 / 2) * trace ((lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace i)) τ)⁻¹ *
        lGramDeriv W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace i)) τ) *
        lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace i)) τ) τ := by
  obtain ⟨ht, hg, hY⟩ := lGram_hypotheses hV hK hKW hβ hgeo hZ₀V hτ.1
  have hmem : Real.sqrt ⁻¹' (K ∩ Ioo (H.regularizedStageStart T W.a j.val)
      (H.regularizedStageEnd T W.b j.val)) ∈ 𝓝 τ :=
    Real.continuous_sqrt.continuousAt.preimage_mem_nhds ((hK.inter isOpen_Ioo).mem_nhds hτ)
  refine (lJacobianDen_hasDeriv W.S W.solution T _ _ τ ht hg hY hpos).congr_of_eventuallyEq ?_
  filter_upwards [hmem] with τ' h'
  exact historyLJacobianDensity_eq_lJacobianDensity (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hK
    hKW hβ hrep j h'

include hV hZ₀V hK hKW hβ hgeo in
theorem continuousAt_lJacobianDensity_sq {s : ℝ} (hs : s ∈ K) :
    ContinuousAt (fun r => lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
      (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
        (chartModelBasis ThreeSpace i)) (r ^ 2)) s := by
  have hs0 : 0 ≤ s := W.nonneg.trans (hKW hs).1.le
  obtain ⟨ht, hg, hY⟩ := lGram_hypotheses hV hK hKW hβ hgeo hZ₀V (τ := s ^ 2)
    (by rw [Real.sqrt_sq hs0]; exact hs)
  have hG : ContinuousAt (fun τ => lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
      (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
        (chartModelBasis ThreeSpace i)) τ) (s ^ 2) :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
      (lGram_hasDeriv W.S W.solution T _ _ (s ^ 2) ht hg hY a b).continuousAt
  have hD := Real.continuous_sqrt.continuousAt.comp
    ((continuous_id.matrix_det).continuousAt.comp hG)
  exact hD.comp (f := fun r : ℝ => r ^ 2) (continuous_pow 2).continuousAt

include hV hZ₀V hK hKW hβ hgeo hrep in
theorem tendsto_historyLJacobianDensity (j : H.StageInterval lo hi) {s₀ : ℝ} (hs₀ : s₀ ∈ K)
    {l : Filter ℝ} (hl : l ≤ 𝓝 s₀)
    (hpiece : ∀ᶠ r in l,
      r ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) :
    Tendsto (H.historyLJacobianDensity hle T v p Z₀
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩) l
      (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) (s₀ ^ 2))) := by
  refine ((continuousAt_lJacobianDensity_sq hV hZ₀V hK hKW hβ hgeo hs₀).tendsto.mono_left
    hl).congr' ?_
  filter_upwards [hl (hK.mem_nhds hs₀), hpiece] with r hrK hrp
  exact (historyLJacobianDensity_eq_lJacobianDensity_sq (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom
    hK hKW hβ hrep j ⟨hrK, hrp⟩).symm

end Window

section Seam

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier} {Z₀ : H.historyLExpDomain hle T v p} {i : Fin H.eventCount}
  {hlo : first ≤ i.castSucc} {hhi : i.succ ≤ last} {W : H.LWindow i.castSucc i.succ T}
  {V : Set ThreeSpace} {K : Set ℝ} {β : ThreeSpace × ℝ → W.X}
  (hV : IsOpen V) (hZ₀V : Z₀.1 ∈ V)
  (hVdom : ∀ Z ∈ V, (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p)
  (hK : IsOpen K) (hKW : K ⊆ Ioo W.a W.b)
  (hβ : ContMDiffOn (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ThreeModel ∞ β (V ×ˢ K))
  (hgeo : ∀ Z ∈ V, IsLRegularizedGeodesicOn W.S T (fun r => β (Z, r)) K)
  (hrep : ∀ Z (hZ : Z ∈ V) (j : H.StageInterval i.castSucc i.succ),
    ∀ r ∈ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val),
      H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r = W.f j (β (Z, r)))

include hV hZ₀V hK hKW hβ hgeo hrep in
theorem tendsto_historyLJacobianDensity_seam (hw : Real.sqrt (T - H.time i.succ) ∈ K) :
    Tendsto (H.historyLJacobianDensity hle T v p Z₀
        ⟨i.succ, hlo.trans i.castSucc_lt_succ.le, hhi⟩)
        (𝓝[<] Real.sqrt (T - H.time i.succ))
        (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace k)) (Real.sqrt (T - H.time i.succ) ^ 2))) ∧
      Tendsto (H.historyLJacobianDensity hle T v p Z₀
        ⟨i.castSucc, hlo, i.castSucc_lt_succ.le.trans hhi⟩)
        (𝓝[>] Real.sqrt (T - H.time i.succ))
        (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace k)) (Real.sqrt (T - H.time i.succ) ^ 2))) := by
  have haw := (hKW hw).1
  have hwb := (hKW hw).2
  constructor
  · refine tendsto_historyLJacobianDensity (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hK hKW hβ hgeo
      hrep ⟨i.succ, i.castSucc_lt_succ.le, le_rfl⟩ hw nhdsWithin_le_nhds ?_
    change ∀ᶠ r in _, r ∈ Ioo (H.regularizedStageStart T W.a i.succ)
      (H.regularizedStageEnd T W.b i.succ)
    rw [W.regularizedStageStart_succ_eq, W.regularizedStageEnd_succ_eq]
    exact Ioo_mem_nhdsLT haw
  · refine tendsto_historyLJacobianDensity (hlo := hlo) (hhi := hhi) hV hZ₀V hVdom hK hKW hβ hgeo
      hrep ⟨i.castSucc, le_rfl, i.castSucc_lt_succ.le⟩ hw nhdsWithin_le_nhds ?_
    change ∀ᶠ r in _, r ∈ Ioo (H.regularizedStageStart T W.a i.castSucc)
      (H.regularizedStageEnd T W.b i.castSucc)
    rw [W.regularizedStageStart_castSucc_eq, W.regularizedStageEnd_castSucc_eq]
    exact Ioo_mem_nhdsGT hwb

end Seam

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
