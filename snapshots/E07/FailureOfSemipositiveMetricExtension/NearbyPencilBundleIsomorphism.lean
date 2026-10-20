import FailureOfSemipositiveMetricExtension.NearbyPencilBundleEquivalence

/-! The evaluation bundle equivalence is analytic in both directions. This proves
L_t is the actual pullback of O(1), rather than just an equality of formal degrees. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
noncomputable section
open Set Bundle IsManifold Topology
open FixedFiberBundle
open scoped Manifold ContDiff

def pencilPatch (t : ℂ) (i : Index) (k : Fin 2) : Set (Fiber t) :=
  baseSet t i ∩ pencilMap t ⁻¹' ProjectiveLine.chartSet k

theorem pencilPatch_isOpen (t : ℂ) (ht : t ≠ 0) (i : Index) (k : Fin 2) :
    IsOpen (pencilPatch t i k) :=
  (baseSet_isOpen t i).inter ((ProjectiveLine.chartSet_isOpen k).preimage (pencilMap_continuous t ht))

theorem pencilPatch_coefficient_ne_zero (t : ℂ) (ht : t ≠ 0) (i : Index) (k : Fin 2)
    (p : Fiber t) (hp : p ∈ pencilPatch t i k) : (pencilSection t k).coefficient i p ≠ 0 :=
  (pencilMap_chartSet_iff t ht i k p hp.1).mp hp.2

theorem pencilPatch_inverse_analytic (t : ℂ) (ht : t ≠ 0) (i : Index) (k : Fin 2) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
      (fun p => ((pencilSection t k).coefficient i p)⁻¹) (pencilPatch t i k) := by
  have h : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} := contDiffOn_id.inv (fun _ h => h)
  exact h.contMDiffOn.comp ((pencilSection t k).analytic i |>.mono inter_subset_left)
    (fun p hp => pencilPatch_coefficient_ne_zero t ht i k p hp)

theorem pencilBundleEquiv_contMDiff (t : ℂ) (ht : t ≠ 0) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (pencilBundleEquiv t ht) := by
  intro z
  let i := (lineCore t).indexAt z.proj
  let k := selectedCoordinate t z.proj
  have hi : z.proj ∈ baseSet t i := (lineCore t).mem_baseSet_at z.proj
  have hk : pencilMap t z.proj ∈ ProjectiveLine.chartSet k := selectedCoordinate_mem t z.proj
  let el := (lineCore t).localTriv i
  let ep := pullbackTriv t ht k
  haveI : MemTrivializationAtlas el := ⟨⟨i,rfl⟩⟩
  apply (ep.contMDiffAt_iff (show pencilBundleEquiv t ht z ∈ ep.source from hk)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (lineCore t).Fiber
  · have hF := ((pencilPatch_inverse_analytic t ht i k).contMDiffAt
        ((pencilPatch_isOpen t ht i k).mem_nhds ⟨hi,hk⟩)).comp z (Bundle.contMDiffAt_proj (lineCore t).Fiber)
    have hL : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ))
        (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω el z :=
      el.contMDiffOn.contMDiffAt (el.open_source.mem_nhds hi)
    apply (hL.snd.smul hF).congr_of_eventuallyEq
    have hU := ((pencilPatch_isOpen t ht i k).preimage
      (FiberBundle.continuous_proj ℂ (lineCore t).Fiber)).mem_nhds ⟨hi,hk⟩
    filter_upwards [hU] with w hw
    simpa only [div_eq_mul_inv,smul_eq_mul] using
      congrArg Prod.snd (pencilBundleEquiv_localTriv t ht i k w hw.1 hw.2)

theorem pencilBundleEquiv_symm_contMDiff (t : ℂ) (ht : t ≠ 0) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (pencilBundleEquiv t ht).symm := by
  intro z
  let i := (lineCore t).indexAt z.proj
  let k := selectedCoordinate t z.proj
  have hi : z.proj ∈ baseSet t i := (lineCore t).mem_baseSet_at z.proj
  have hk : pencilMap t z.proj ∈ ProjectiveLine.chartSet k := selectedCoordinate_mem t z.proj
  let el := (lineCore t).localTriv i
  let ep := pullbackTriv t ht k
  haveI : MemTrivializationAtlas el := ⟨⟨i,rfl⟩⟩
  apply (el.contMDiffAt_iff (show (pencilBundleEquiv t ht).symm z ∈ el.source from hi)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (PullbackFiber t ht)
  · have hF := ((pencilSection t k).analytic i |>.contMDiffAt
        ((baseSet_isOpen t i).mem_nhds hi)).comp z (Bundle.contMDiffAt_proj (PullbackFiber t ht))
    have hP : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ))
        (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hk)
    apply (hF.smul hP.snd).congr_of_eventuallyEq
    have hU := ((pencilPatch_isOpen t ht i k).preimage
      (FiberBundle.continuous_proj ℂ (PullbackFiber t ht))).mem_nhds ⟨hi,hk⟩
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (pencilBundleEquiv_symm_localTriv t ht i k w hw.1 hw.2)

/-- A genuine analytic bundle isomorphism L_t ≃ pencilMap_t^* O(1), for t nonzero. -/
def pencilBundleHomeomorph (t : ℂ) (ht : t ≠ 0) : (lineCore t).TotalSpace ≃ₜ PullbackTotal t ht where
  toEquiv := pencilBundleEquiv t ht
  continuous_toFun := (pencilBundleEquiv_contMDiff t ht).continuous
  continuous_invFun := (pencilBundleEquiv_symm_contMDiff t ht).continuous

theorem pencilBundleHomeomorph_analytic (t : ℂ) (ht : t ≠ 0) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (pencilBundleHomeomorph t ht) ∧
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (pencilBundleHomeomorph t ht).symm :=
  ⟨pencilBundleEquiv_contMDiff t ht,pencilBundleEquiv_symm_contMDiff t ht⟩

/-- The two generating sections acquire precisely the normalized homogeneous
coordinate coefficients under the actual pullback isomorphism. -/
theorem pencilBundleEquiv_section_localTriv (t : ℂ) (ht : t ≠ 0) (i : Index) (k l : Fin 2)
    (p : Fiber t) (hi : p ∈ baseSet t i) (hk : pencilMap t p ∈ ProjectiveLine.chartSet k) :
    pullbackTriv t ht k (pencilBundleEquiv t ht (sectionMap (pencilSection t l) p)) =
      (p,(pencilSection t l).coefficient i p / (pencilSection t k).coefficient i p) := by
  have hs : ((lineCore t).localTriv i (sectionMap (pencilSection t l) p)).2 =
      (pencilSection t l).coefficient i p :=
    congrArg Prod.snd (sectionMap_localTriv (pencilSection t l) i p hi)
  calc
    _ = (p,((lineCore t).localTriv i (sectionMap (pencilSection t l) p)).2 /
        (pencilSection t k).coefficient i p) :=
      pencilBundleEquiv_localTriv t ht i k (sectionMap (pencilSection t l) p) hi hk
    _ = _ := congrArg (fun c : ℂ => (p,c / (pencilSection t k).coefficient i p)) hs

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
