import DifferentialGeometry.Geometry.Comparison.Soul.NormalTube
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceLevelProduct
import DifferentialGeometry.Geometry.Comparison.Soul.SmoothFlowCrossing
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false
noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

section Gluing

variable {EM EN : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [CompleteSpace EM]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HM HN : Type*} [TopologicalSpace HM] [TopologicalSpace HN]
  {I : ModelWithCorners ℝ EM HM} [I.Boundaryless]
  {J : ModelWithCorners ℝ EN HN}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace HN N]

private theorem radial_gluing_diffeomorph
    (L : N → ℝ) (hLc : Continuous L)
    (hLs : ∀ z, 0 < L z → ContMDiffAt J 𝓘(ℝ, ℝ) ∞ L z)
    (scale : ℝ → N → N)
    (hscale : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun z : ℝ × N => scale z.1 z.2))
    (hone : ∀ z, scale 1 z = z)
    (hmul : ∀ a b z, scale a (scale b z) = scale (a * b) z)
    (hlength : ∀ a, 0 ≤ a → ∀ z, L (scale a z) = a * L z)
    (d : M → ℝ) (hdc : Continuous d)
    {ε ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδℓ : δ < ℓ) (hε : ℓ + δ < ε)
    (Φ : PartialDiffeomorph J I N M ∞)
    (hsource : Φ.source = {z | L z < ε}) (htarget : Φ.target = {q | d q < ε})
    (hradius : ∀ z ∈ Φ.source, L z = d (Φ z))
    (ϕ : Flow ℝ M)
    (hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2))
    (hinc : ∀ q, ℓ ≤ d q → ∀ t : ℝ, 0 < t → d q < d (ϕ t q))
    (hcross : ∀ q, ℓ ≤ d q → ∃! t : ℝ, d (ϕ t q) = ℓ)
    (hrad : ∀ z, ℓ - δ < L z → L z < ℓ + δ →
      ϕ (L z - ℓ) (Φ (scale (ℓ / L z) z)) = Φ z) :
    ∃ e : N ≃ₘ⟮J, I⟯ M, ∀ z,
      e z = if L z ≤ ℓ then Φ z else ϕ (L z - ℓ) (Φ (scale (ℓ / L z) z)) := by
  classical
  have hℓε : ℓ < ε := (lt_add_of_pos_right ℓ hδ).trans hε
  have hΦleft (z : N) (hz : z ∈ Φ.source) : Φ.symm (Φ z) = z :=
    Φ.toPartialEquiv.left_inv hz
  have hΦright (q : M) (hq : q ∈ Φ.target) : Φ (Φ.symm q) = q :=
    Φ.toPartialEquiv.right_inv hq
  let n : N → N := fun z => scale (ℓ / L z) z
  have hnL (z : N) (hz : 0 < L z) : L (n z) = ℓ := by
    change L (scale (ℓ / L z) z) = ℓ
    rw [hlength _ (div_nonneg hℓ.le hz.le), div_mul_cancel₀ _ hz.ne']
  have hnS (z : N) (hz : 0 < L z) : n z ∈ Φ.source := by
    rw [hsource]
    change L (n z) < ε
    rw [hnL z hz]
    exact hℓε
  have hdn (z : N) (hz : 0 < L z) : d (Φ (n z)) = ℓ :=
    (hradius _ (hnS z hz)).symm.trans (hnL z hz)
  have hscale_n (z : N) (hz : 0 < L z) : scale (L z / ℓ) (n z) = z := by
    dsimp only [n]
    rw [hmul]
    have hc : L z / ℓ * (ℓ / L z) = 1 := by
      rw [div_mul_div_cancel₀ hℓ.ne', div_self hz.ne']
    rw [hc, hone]
  have hn_scale (z : N) (hz : L z = ℓ) (r : ℝ) (hr : 0 < r) :
      n (scale (r / ℓ) z) = z := by
    have hlen : L (scale (r / ℓ) z) = r := by
      rw [hlength _ (div_nonneg hr.le hℓ.le), hz, div_mul_cancel₀ _ hℓ.ne']
    dsimp only [n]
    rw [hlen, hmul]
    have hc : ℓ / r * (r / ℓ) = 1 := by
      rw [div_mul_div_cancel₀ hr.ne', div_self hℓ.ne']
    rw [hc, hone]
  have hLinv (q : M) (hq : d q < ε) : L (Φ.symm q) = d q := by
    have hqT : q ∈ Φ.target := by rwa [htarget]
    exact (hradius (Φ.symm q) (Φ.map_target hqT)).trans (congrArg d (hΦright q hqT))
  let τ : M → ℝ := fun q => if hq : ℓ ≤ d q then (hcross q hq).choose else 0
  have hτ (q : M) (hq : ℓ ≤ d q) : d (ϕ (τ q) q) = ℓ := by
    simpa only [τ, dif_pos hq] using (hcross q hq).choose_spec.1
  have hτunique (q : M) (hq : ℓ ≤ d q) (t : ℝ) (ht : d (ϕ t q) = ℓ) : t = τ q := by
    simpa only [τ, dif_pos hq] using (hcross q hq).choose_spec.2 t ht
  have hτnonpos (q : M) (hq : ℓ ≤ d q) : τ q ≤ 0 := by
    by_contra h
    have hh := hinc q hq (τ q) (lt_of_not_ge h)
    rw [hτ q hq] at hh
    exact (not_lt_of_ge hq) hh
  have hτneg (q : M) (hq : ℓ < d q) : τ q < 0 := by
    have hn := hτnonpos q hq.le
    have hne : τ q ≠ 0 := by
      intro h
      have hh := hτ q hq.le
      rw [h, ϕ.map_zero_apply] at hh
      exact (ne_of_gt hq) hh
    exact lt_of_le_of_ne hn hne
  let F : N → M := fun z => if L z ≤ ℓ then Φ z else ϕ (L z - ℓ) (Φ (n z))
  let G : M → N := fun q => if d q ≤ ℓ then Φ.symm q else
    scale ((ℓ - τ q) / ℓ) (Φ.symm (ϕ (τ q) q))
  have hFinner (z : N) (hz : L z < ℓ + δ) : F z = Φ z := by
    dsimp only [F]
    split_ifs with h
    · rfl
    · exact hrad z (by linarith only [lt_of_not_ge h, hδ]) hz
  have hFouter (z : N) (hz : ℓ < L z) : F z = ϕ (L z - ℓ) (Φ (n z)) :=
    if_neg (not_le_of_gt hz)
  have hFdist (z : N) (hz : ℓ < L z) : ℓ < d (F z) := by
    rw [hFouter z hz]
    have hh := hinc (Φ (n z))
      (by simpa only [hdn z (hℓ.trans hz)] using (le_rfl : ℓ ≤ ℓ))
      (L z - ℓ) (sub_pos.mpr hz)
    rwa [hdn z (hℓ.trans hz)] at hh
  have hGF : LeftInverse G F := by
    intro z
    by_cases hz : L z ≤ ℓ
    · have hzS : z ∈ Φ.source := by rw [hsource]; exact hz.trans_lt hℓε
      have hd : d (Φ z) ≤ ℓ := by rw [← hradius z hzS]; exact hz
      change G (F z) = z
      rw [show F z = Φ z from if_pos hz]
      change (if d (Φ z) ≤ ℓ then Φ.symm (Φ z) else _) = z
      rw [if_pos hd, hΦleft z hzS]
    · have hz' := lt_of_not_ge hz
      have hdz := hFdist z hz'
      have ht : -(L z - ℓ) = τ (F z) := hτunique (F z) hdz.le _ (by
        rw [hFouter z hz', ← ϕ.map_add, neg_add_cancel, ϕ.map_zero_apply]
        exact hdn z (hℓ.trans hz'))
      change (if d (F z) ≤ ℓ then _ else _) = z
      rw [if_neg (not_le_of_gt hdz), ← ht, hFouter z hz', ← ϕ.map_add,
        neg_add_cancel, ϕ.map_zero_apply, hΦleft _ (hnS z (hℓ.trans hz'))]
      have hc : (ℓ - -(L z - ℓ)) / ℓ = L z / ℓ := by ring
      rw [hc]
      exact hscale_n z (hℓ.trans hz')
  have hFG : RightInverse G F := by
    intro q
    by_cases hq : d q ≤ ℓ
    · have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.trans_lt hℓε
      have hz : L (Φ.symm q) ≤ ℓ := by rw [hLinv q (hq.trans_lt hℓε)]; exact hq
      change F (if d q ≤ ℓ then _ else _) = q
      rw [if_pos hq]
      change (if L (Φ.symm q) ≤ ℓ then _ else _) = q
      rw [if_pos hz, hΦright q hqT]
    · have hq' := lt_of_not_ge hq
      let z := Φ.symm (ϕ (τ q) q)
      have hyT : ϕ (τ q) q ∈ Φ.target := by
        rw [htarget]
        change d (ϕ (τ q) q) < ε
        rw [hτ q hq'.le]
        exact hℓε
      have hzL : L z = ℓ := (hLinv _ (by rw [hτ q hq'.le]; exact hℓε)).trans (hτ q hq'.le)
      have hr : ℓ < ℓ - τ q := by linarith only [hτneg q hq']
      have hGq : G q = scale ((ℓ - τ q) / ℓ) z := if_neg hq
      have hLG : L (G q) = ℓ - τ q := by
        rw [hGq, hlength _ (div_nonneg (hℓ.trans hr).le hℓ.le), hzL,
          div_mul_cancel₀ _ hℓ.ne']
      rw [hFouter (G q) (by rw [hLG]; exact hr), hLG, hGq,
        hn_scale z hzL _ (hℓ.trans hr)]
      have htime : ℓ - τ q - ℓ = -τ q := by ring
      rw [htime, show Φ z = ϕ (τ q) q from hΦright _ hyT,
        ← ϕ.map_add, neg_add_cancel, ϕ.map_zero_apply]
  have hGinner (q : M) (hq : d q < ℓ + δ) : G q = Φ.symm q := by
    have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.trans hε
    have hz : L (Φ.symm q) < ℓ + δ := (hLinv q (hq.trans hε)).trans_lt hq
    have hh := hGF (Φ.symm q)
    rwa [hFinner _ hz, hΦright q hqT] at hh
  have hnSmooth (z : N) (hz : 0 < L z) : ContMDiffAt J J ∞ n z :=
    hscale.contMDiffAt.comp z
      ((contMDiffAt_const.div₀ (hLs z hz) hz.ne').prodMk contMDiffAt_id)
  have hFsmooth : ContMDiff J I ∞ F := by
    intro z
    by_cases hz : L z < ℓ + δ
    · have hzS : z ∈ Φ.source := by rw [hsource]; exact hz.trans hε
      apply (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hzS)).congr_of_eventuallyEq
      filter_upwards [hLc.continuousAt (Iio_mem_nhds hz)] with w hw
      exact hFinner w hw
    · have hz' : ℓ < L z := by linarith only [le_of_not_gt hz, hδ]
      have hn := hnSmooth z (hℓ.trans hz')
      have hΦn := (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hnS z (hℓ.trans hz')))).comp z hn
      have hs : ContMDiffAt J I ∞ (fun w => ϕ (L w - ℓ) (Φ (n w))) z :=
        hϕ.contMDiffAt.comp z (((hLs z (hℓ.trans hz')).sub contMDiffAt_const).prodMk hΦn)
      apply hs.congr_of_eventuallyEq
      filter_upwards [hLc.continuousAt (Ioi_mem_nhds hz')] with w hw
      exact hFouter w hw
  have hradDist (z : N) (hz : L z = ℓ) (s : ℝ) (hs : s ∈ Ioo (-δ) δ) :
      d (ϕ s (Φ z)) = ℓ + s := by
    have hrs : 0 < ℓ + s := by linarith only [hs.1, hδℓ]
    let w := scale ((ℓ + s) / ℓ) z
    have hwL : L w = ℓ + s := by
      rw [hlength _ (div_nonneg hrs.le hℓ.le), hz, div_mul_cancel₀ _ hℓ.ne']
    have hwS : w ∈ Φ.source := by
      rw [hsource]
      change L w < ε
      rw [hwL]
      linarith only [hs.2, hε]
    have hradw := hrad w (by rw [hwL]; linarith only [hs.1])
      (by rw [hwL]; linarith only [hs.2])
    have hnw : n w = z := hn_scale z hz _ hrs
    change ϕ (L w - ℓ) (Φ (n w)) = Φ w at hradw
    rw [hwL, add_sub_cancel_left, hnw] at hradw
    rw [hradw, ← hradius w hwS, hwL]
  let U : Set M := {q | 0 < d q ∧ d q < ε}
  have hU : IsOpen U := (isOpen_lt continuous_const hdc).inter (isOpen_lt hdc continuous_const)
  have hds : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ d U := by
    intro q hq
    have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.2
    have hpos : 0 < L (Φ.symm q) := by rw [hLinv q hq.2]; exact hq.1
    have hh := (hLs (Φ.symm q) hpos).comp q
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hqT))
    apply (hh.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [Φ.open_target.mem_nhds hqT] with x hx
    exact (hLinv x (by rwa [htarget] at hx)).symm
  have htrans (q : M) (t : ℝ) (ht : d (ϕ t q) = ℓ) :
      HasDerivAt (fun s => d (ϕ s q)) 1 t := by
    have hyT : ϕ t q ∈ Φ.target := by
      rw [htarget]
      change d (ϕ t q) < ε
      rw [ht]
      exact hℓε
    let z := Φ.symm (ϕ t q)
    have hz : L z = ℓ := (hLinv _ (by rw [ht]; exact hℓε)).trans ht
    have hzero : HasDerivAt (fun s => d (ϕ s (ϕ t q))) 1 0 := by
      have hlin : HasDerivAt (fun s : ℝ => ℓ + s) 1 0 := by
        convert! (hasDerivAt_id (0 : ℝ)).const_add ℓ
      apply hlin.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with s hs
      simpa only [show Φ z = ϕ t q from hΦright _ hyT] using hradDist z hz s hs
    have hshift : HasDerivAt (fun s : ℝ => s - t) 1 t := by
      convert! (hasDerivAt_id t).sub_const t
    have hh : HasDerivAt (fun s => d (ϕ (s - t) (ϕ t q))) (1 * 1) t :=
      hzero.comp_of_eq t hshift (sub_self t).symm
    simpa only [Function.comp_apply, ← ϕ.map_add, sub_add_cancel, one_mul] using hh
  have hGsmooth : ContMDiff I J ∞ G := by
    intro q
    by_cases hq : d q < ℓ + δ
    · have hqT : q ∈ Φ.target := by rw [htarget]; exact hq.trans hε
      apply (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hqT)).congr_of_eventuallyEq
      filter_upwards [hdc.continuousAt (Iio_mem_nhds hq)] with x hx
      exact hGinner x hx
    · have hq' : ℓ < d q := by linarith only [le_of_not_gt hq, hδ]
      have hyU : ϕ (τ q) q ∈ U := by change 0 < d _ ∧ d _ < ε; rw [hτ q hq'.le]; exact ⟨hℓ, hℓε⟩
      obtain ⟨σ, W, hW, hqW, hσ, _, heq, _, _⟩ :=
        exists_smooth_extension_unique_flow_levelTime ϕ hϕ hU hds τ {x | ℓ ≤ d x} ℓ
          hyU (hτ q hq'.le) (htrans q (τ q) (hτ q hq'.le)) one_ne_zero
          (fun x hx t ht => hτunique x hx t ht)
      have hτs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ τ q := by
        apply (hσ.contMDiffAt (hW.mem_nhds hqW)).congr_of_eventuallyEq
        filter_upwards [hW.mem_nhds hqW, hdc.continuousAt (Ioi_mem_nhds hq')] with x hxW hx
        change ℓ < d x at hx
        exact heq ⟨hxW, by change ℓ ≤ d x; exact hx.le⟩
      have hys : ContMDiffAt I I ∞ (fun x => ϕ (τ x) x) q :=
        hϕ.contMDiffAt.comp q (hτs.prodMk contMDiffAt_id)
      have hyT : ϕ (τ q) q ∈ Φ.target := by
        rw [htarget]
        change d (ϕ (τ q) q) < ε
        rw [hτ q hq'.le]
        exact hℓε
      have hzs : ContMDiffAt I J ∞ (fun x => Φ.symm (ϕ (τ x) x)) q :=
        (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hyT)).comp
          (f := fun x => ϕ (τ x) x) q hys
      have hs : ContMDiffAt I J ∞
          (fun x => scale ((ℓ - τ x) / ℓ) (Φ.symm (ϕ (τ x) x))) q :=
        hscale.contMDiffAt.comp q
          (((contMDiffAt_const.sub hτs).div_const ℓ).prodMk hzs)
      apply hs.congr_of_eventuallyEq
      filter_upwards [hdc.continuousAt (Ioi_mem_nhds hq')] with x hx
      exact if_neg (not_le_of_gt hx)
  let e : N ≃ₘ⟮J, I⟯ M :=
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      contMDiff_toFun := hFsmooth
      contMDiff_invFun := hGsmooth }
  exact ⟨e, fun _ => rfl⟩

end Gluing

section FiberScaling

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

private theorem totalSpace_scaling_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) ∞
      (fun z : ℝ × TotalSpace F V => (⟨z.2.proj, z.1 • z.2.snd⟩ : TotalSpace F V)) := by
  intro z
  have hs : ContMDiffAt (𝓘(ℝ, ℝ).prod (IB.prod 𝓘(ℝ, F))) (IB.prod 𝓘(ℝ, F)) ∞
      (Prod.snd : ℝ × TotalSpace F V → TotalSpace F V) z := contMDiffAt_snd
  obtain ⟨hb, hv⟩ := Bundle.contMDiffAt_totalSpace.mp hs
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hb, (contMDiffAt_fst.smul hv).congr_of_eventuallyEq ?_⟩
  let e := trivializationAt F V z.2.proj
  have he : ∀ᶠ y : ℝ × TotalSpace F V in 𝓝 z, y.2.proj ∈ e.baseSet :=
    hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V z.2.proj))
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul y.1 y.2.snd

end FiberScaling

section NormalBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
  {S : Set M}

local notation "FN" => (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
local notation "IN" => ModelWithCorners.prod
  (modelWithCornersSelf ℝ (Fin (maxSliceDim I S) → ℝ))
  (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
local notation "NB" => TotalSpace FN (normalBundleFiber (I := I) g S)

def normalFlowMap (S : Set M) (ϕ : Flow ℝ M) (ℓ : ℝ) :
    TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber (I := I) g S) → M := fun z =>
  let r := Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)
  if r ≤ ℓ then normalExp (I := I) g hEnorm S z else
    ϕ (r - ℓ) (normalExp (I := I) g hEnorm S ⟨z.proj, (ℓ / r) • z.snd⟩)

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
@[simp] theorem normalFlowMap_zero (ϕ : Flow ℝ M) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (p : S) :
    normalFlowMap (I := I) g hEnorm S ϕ ℓ ⟨p, 0⟩ = p.1 := by
  simp only [normalFlowMap, Submodule.coe_zero, map_zero, Real.sqrt_zero, if_pos hℓ,
    normalExp_zero]

theorem exists_normalFlow_diffeomorph
    (hSne : S.Nonempty) (hScomp : IsCompact S) (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅)
    {ε ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδℓ : δ < ℓ) (hε : ℓ + δ < ε)
    (V : (x : M) → TangentSpace I x)
    (hV : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (ϕ : Flow ℝ M)
    (hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2))
    (hIntegral : ∀ q, IsMIntegralCurve (fun t => ϕ t q) V)
    (hout : ∀ q : M, ℓ ≤ Metric.infDist q S → ∀ u : TangentSpace I q,
      g.inner q u u = 1 → intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
        g.inner q (V q) u < 0) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ∀ Φ : PartialDiffeomorph IN I NB M ∞,
      Φ.source = {z | Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ε} →
      Φ.target = {q | Metric.infDist q S < ε} →
      (Φ : NB → M) = normalExp (I := I) g hEnorm S →
      (∀ z ∈ Φ.source,
        Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) = Metric.infDist (Φ z) S) →
      (∀ z : NB, ℓ - δ < Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) →
        Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) < ℓ + δ →
        ϕ (Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1) - ℓ)
          (normalExp (I := I) g hEnorm S
            ⟨z.proj, (ℓ / Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)) • z.snd⟩) =
          normalExp (I := I) g hEnorm S z) →
      ∃ e : NB ≃ₘ⟮IN, I⟯ M,
        (∀ z, e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z) ∧
        ∀ p : S, e ⟨p, 0⟩ = p.1 := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  dsimp only
  intro Φ hsource htarget hΦ hradius hrad
  let L : NB → ℝ := fun z => Real.sqrt (g.inner z.proj.1 z.snd.1 z.snd.1)
  let scale : ℝ → NB → NB := fun r z => ⟨z.proj, r • z.snd⟩
  have hLc : Continuous L := normalLength_continuous g hEnorm hconv hB
  have hQ : ContMDiff IN 𝓘(ℝ, ℝ) ∞
      (fun z : NB => g.inner z.proj.1 z.snd.1 z.snd.1) :=
    (tangentSquaredLength_contMDiff g).comp (normalBundleInclusion_contMDiff g hEnorm hconv hB)
  have hLs (z : NB) (hz : 0 < L z) : ContMDiffAt IN 𝓘(ℝ, ℝ) ∞ L z :=
    (Real.contDiffAt_sqrt (Real.sqrt_pos.mp hz).ne').contMDiffAt.comp z (hQ z)
  have hscale : ContMDiff (𝓘(ℝ, ℝ).prod IN) IN ∞ (fun z : ℝ × NB => scale z.1 z.2) :=
    totalSpace_scaling_contMDiff
  have hone (z : NB) : scale 1 z = z := by
    cases z
    simp only [scale, one_smul]
  have hmul (r s : ℝ) (z : NB) : scale r (scale s z) = scale (r * s) z := by
    simp only [scale, smul_smul]
  have hlength (r : ℝ) (hr : 0 ≤ r) (z : NB) : L (scale r z) = r * L z :=
    sqrt_gInner_smul_self (I := I) g z.proj.1 hr z.snd.1
  have hinc (q : M) (hq : ℓ ≤ Metric.infDist q S) (t : ℝ) (ht : 0 < t) :
      Metric.infDist q S < Metric.infDist (ϕ t q) S := by
    have hm := infDist_strictMonoOn_of_outward_integralCurve g hEnorm hScomp hSne V hV
      (hIntegral q) hℓ hout (by simpa only [ϕ.map_zero_apply] using hq)
    simpa only [ϕ.map_zero_apply] using hm
      (by change (0 : ℝ) ≤ 0; exact le_rfl) (by change 0 ≤ t; exact ht.le) ht
  have hcross (q : M) (hq : ℓ ≤ Metric.infDist q S) :
      ∃! t : ℝ, Metric.infDist (ϕ t q) S = ℓ :=
    existsUnique_infDist_levelTime g hEnorm hScomp hSne V hV ϕ hIntegral hℓ hout q hq ℓ le_rfl
  obtain ⟨e, he⟩ := radial_gluing_diffeomorph L hLc hLs scale hscale hone hmul hlength
    (fun q => Metric.infDist q S) (Metric.continuous_infDist_pt S) hℓ hδ hδℓ hε
    Φ hsource htarget hradius ϕ hϕ hinc hcross (by
      intro z hzlo hzhi
      simpa only [hΦ] using hrad z hzlo hzhi)
  have hemap (z : NB) : e z = normalFlowMap (I := I) g hEnorm S ϕ ℓ z := by
    simpa only [normalFlowMap, L, scale, hΦ] using he z
  refine ⟨e, hemap, ?_⟩
  intro p
  rw [hemap, normalFlowMap_zero g hEnorm ϕ hℓ.le]

end NormalBundle

end DifferentialGeometry.Geometry.Topology
