import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalIsomorphism
import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalForms
import FailureOfSemipositiveMetricExtension.CentralAdjointSection

/-! Actual analytic adjoint bundles glued by the product of the verified canonical
Jacobian cocycle and the m-th power of the actual L cocycle.  The previously
constructed nonzero sigma is transported into the m=4 bundle as an actual section. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

def adjointGain (t : ℂ) (m : ℕ) (d c : DivisionIndex) (p : Fiber t) : ℂ :=
  FixedFiber.canonicalGain t (divisionChart d) (divisionChart c) p *
    gain t (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) p ^ m

theorem adjointGain_contMDiffOn (t : ℂ) (m : ℕ) (d c : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (adjointGain t m d c)
      (divisionPatch t d ∩ divisionPatch t c) := by
  have hk := (FixedFiber.chartJacobian_contMDiffOn t c.1 d.1 c.2.1 d.2.1).mono
    (show divisionPatch t d ∩ divisionPatch t c ⊆ FixedFiber.source t c.1 c.2.1 ∩ FixedFiber.source t d.1 d.2.1 from
      fun _ h => ⟨h.2.1,h.1.1⟩)
  have hl := (gain_contMDiffOn t (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) ω).mono
    (show divisionPatch t d ∩ divisionPatch t c ⊆ baseSet t (divisionFrame d) ∩ baseSet t (divisionFrame c) from
      fun _ h => ⟨h.1.2,h.2.2⟩)
  exact hk.smul (scalarPower_contMDiffOn hl m)

/-- The product-cocycle line bundle K tensor L^m, on the actual fibre. -/
def adjointCore (t : ℂ) (m : ℕ) : VectorBundleCore ℂ (Fiber t) ℂ DivisionIndex where
  baseSet := divisionPatch t
  isOpen_baseSet := divisionPatch_isOpen t
  indexAt := canonicalPatchAt t
  mem_baseSet_at := canonicalPatchAt_mem t
  coordChange d c p := adjointGain t m d c p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self d p _ v := by simp [adjointGain,gain_self]
  continuousOn_coordChange d c := (adjointGain_contMDiffOn t m d c).continuousOn.smul continuousOn_const
  coordChange_comp d c b p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    change (_ * _^m) * ((_ * _^m) * v) = _
    rw [show ∀ K1 K2 L1 L2 : ℂ, (K1*L1^m)*((K2*L2^m)*v) = (K1*K2)*(L1*L2)^m*v from
      by intros; rw [mul_pow]; ring]
    rw [FixedFiber.canonicalGain_comp t (divisionChart d) (divisionChart c) (divisionChart b) p
      hp.1.1.1 hp.1.2.1 hp.2.1,
      gain_comp t (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) (divisionFrame b) p
        ⟨⟨hp.1.1.2,hp.1.2.2⟩,hp.2.2⟩]
    rfl

instance adjointCore_isContMDiff (t : ℂ) (m : ℕ) : (adjointCore t m).IsContMDiff 𝓘(ℂ,FixedFiber.Coord) ω where
  contMDiffOn_coordChange d c := (adjointGain_contMDiffOn t m d c).smul contMDiffOn_const

theorem adjointCore_finrank (t : ℂ) (m : ℕ) (p : Fiber t) :
    Module.finrank ℂ ((adjointCore t m).Fiber p) = 1 := Module.finrank_self ℂ

theorem adjointCore_analytic (t : ℂ) (m : ℕ) :
    ContMDiffVectorBundle ω ℂ (adjointCore t m).Fiber 𝓘(ℂ,FixedFiber.Coord) := inferInstance

/-- The actual sigma transition is K times four copies of the actual L transition. -/
theorem sigmaGain_canonical_four_L (t : ℂ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) :
    gain t (-7) (fun _ => 3) i j p =
      gain t 1 (fun _ => -1) i j p * gain t (-2) (fun _ => 1) i j p ^ 4 := by
  have h2 : gain t (-4) (fun _ => 2) i j p =
      gain t (-2) (fun _ => 1) i j p * gain t (-2) (fun _ => 1) i j p := by
    simpa using gain_add t (-2) (-2) (fun _ => 1) (fun _ => 1) i j p hp
  have h4 : gain t (-8) (fun _ => 4) i j p =
      gain t (-4) (fun _ => 2) i j p * gain t (-4) (fun _ => 2) i j p := by
    simpa using gain_add t (-4) (-4) (fun _ => 2) (fun _ => 2) i j p hp
  have h : gain t (-7) (fun _ => 3) i j p =
      gain t 1 (fun _ => -1) i j p * gain t (-8) (fun _ => 4) i j p := by
    simpa using gain_add t 1 (-8) (fun _ => -1) (fun _ => 4) i j p hp
  rw [h,h4,h2]
  ring

def sigmaAdjointCoefficient (d : DivisionIndex) (p : Fiber 0) : ℂ :=
  canonicalFactor 0 d p * sigmaSection.coefficient (divisionFrame d) p

theorem sigmaAdjointCoefficient_analytic (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (sigmaAdjointCoefficient d) (divisionPatch 0 d) :=
  (canonicalFactor_contMDiffOn 0 d).smul
    ((sigmaSection.analytic (divisionFrame d)).mono (divisionPatch_subset_frame 0 d))

theorem sigmaAdjointCoefficient_compatible (d c : DivisionIndex) (p : Fiber 0)
    (hd : p ∈ divisionPatch 0 d) (hc : p ∈ divisionPatch 0 c) :
    adjointGain 0 4 d c p * sigmaAdjointCoefficient d p = sigmaAdjointCoefficient c p := by
  change (_ * _^4) * (canonicalFactor 0 d p * _) = _
  calc
    _ = (FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p * canonicalFactor 0 d p) *
      gain 0 (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) p ^ 4 *
        sigmaSection.coefficient (divisionFrame d) p := by ring
    _ = canonicalFactor 0 c p *
      (gain 0 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p *
        gain 0 (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) p ^ 4) *
          sigmaSection.coefficient (divisionFrame d) p := by
      rw [canonicalFactor_transition 0 d c p hd hc]; ring
    _ = canonicalFactor 0 c p *
      (gain 0 (-7) (fun _ => 3) (divisionFrame d) (divisionFrame c) p * sigmaSection.coefficient (divisionFrame d) p) := by
      rw [← sigmaGain_canonical_four_L 0 _ _ p ⟨hd.2,hc.2⟩]; ring
    _ = _ := by rw [sigmaSection.compatible _ _ p ⟨hd.2,hc.2⟩]; rfl

/-- Sigma as a vector in the actual canonical tensor L^4 fibre. -/
def sigmaAdjointValue (p : Fiber 0) : (adjointCore 0 4).Fiber p :=
  sigmaAdjointCoefficient ((adjointCore 0 4).indexAt p) p

def sigmaAdjointMap (p : Fiber 0) : (adjointCore 0 4).TotalSpace := ⟨p,sigmaAdjointValue p⟩

@[simp] theorem sigmaAdjointMap_projects (p : Fiber 0) : (sigmaAdjointMap p).proj = p := rfl

theorem sigmaAdjointMap_localTriv (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    (adjointCore 0 4).localTriv d (sigmaAdjointMap p) = (p,sigmaAdjointCoefficient d p) := by
  rw [VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · exact sigmaAdjointCoefficient_compatible ((adjointCore 0 4).indexAt p) d p ((adjointCore 0 4).mem_baseSet_at p) hp

theorem sigmaAdjointMap_contMDiff :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω sigmaAdjointMap := by
  intro p
  let d := (adjointCore 0 4).indexAt p
  have hp : p ∈ divisionPatch 0 d := (adjointCore 0 4).mem_baseSet_at p
  let e := (adjointCore 0 4).localTriv d
  haveI : MemTrivializationAtlas e := ⟨⟨d,rfl⟩⟩
  apply (e.contMDiffAt_iff (show sigmaAdjointMap p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  exact ((sigmaAdjointCoefficient_analytic d).congr (fun q hq =>
    congrArg Prod.snd (sigmaAdjointMap_localTriv d q hq))).contMDiffAt
    ((divisionPatch_isOpen 0 d).mem_nhds hp)

theorem sigmaAdjointValue_witness_ne_zero : sigmaAdjointValue auxiliaryWitness ≠ 0 := by
  let d := (adjointCore 0 4).indexAt auxiliaryWitness
  have hd := (adjointCore 0 4).mem_baseSet_at auxiliaryWitness
  change canonicalFactor 0 d auxiliaryWitness * sigmaSection.coefficient (divisionFrame d) auxiliaryWitness ≠ 0
  apply mul_ne_zero (canonicalFactor_ne_zero 0 d auxiliaryWitness hd)
  exact fun hz => sigmaSection_witness_ne_zero
    ((sectionValue_zero_iff sigmaSection (divisionFrame d) auxiliaryWitness hd.2).mpr hz)

theorem sigmaAdjoint_nonzero : ∃ p : Fiber 0, sigmaAdjointValue p ≠ 0 :=
  ⟨auxiliaryWitness,sigmaAdjointValue_witness_ne_zero⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
