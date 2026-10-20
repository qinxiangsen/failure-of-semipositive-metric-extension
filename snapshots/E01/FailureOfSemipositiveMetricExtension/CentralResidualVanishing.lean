import FailureOfSemipositiveMetricExtension.CentralTransverseLineDensity

/-! Central vanishing for arbitrary actual analytic sections of any ambient
multidegree bundle. The proof uses the constructed transverse-line bundle isomorphism,
projective-line negative-degree vanishing, and a proved dense generic locus. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem negative_degree_section_zero (a : ℤ) (b : Fin 4 → ℤ)
    (hdeg : restrictionDegree a b < 0)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace)))
    (p : Fiber 0) : s p = 0 := by
  have hz : ∀ q ∈ genericLocus, s q = 0 := by
    intro q hq
    obtain ⟨w,hw,hbase⟩ := hq
    have hv := negative_restriction_section_zero (dataOfVector w hw) a b hdeg s hs
      (Projectivization.mk ℂ ![w 0,w 2] (goodVector_xz_ne_zero w hw))
    have he := param_dataOfVector q w hw hbase
    change s (param (dataOfVector w hw)
      (Projectivization.mk ℂ ![w 0,w 2] (goodVector_xz_ne_zero w hw))) = 0 at hv
    rw [he] at hv
    exact hv
  let i := (FixedFiberBundle.core 0 a b).indexAt p
  let e := (FixedFiberBundle.core 0 a b).localTriv i
  let f : Fiber 0 → ℂ := fun q => (e (⟨q,s q⟩ : (FixedFiberBundle.core 0 a b).TotalSpace)).2
  have hf : ContinuousOn f (FixedFiberBundle.baseSet 0 i) :=
    continuous_snd.comp_continuousOn (e.continuousOn.comp hs.continuous.continuousOn (fun q hq => hq))
  have hz' : EqOn f (fun _ => 0) (genericLocus ∩ FixedFiberBundle.baseSet 0 i) := by
    intro q hq
    change FixedFiberBundle.gain 0 a b ((FixedFiberBundle.core 0 a b).indexAt q) i q * (show ℂ from s q) = 0
    rw [hz q hq.1]
    exact mul_zero _
  have hp := hz'.of_subset_closure hf continuousOn_const inter_subset_right
    (by simpa only [inter_comm] using
      (genericLocus_dense).open_subset_closure_inter (FixedFiberBundle.baseSet_isOpen 0 i))
      ((FixedFiberBundle.core 0 a b).mem_baseSet_at p)
  change FixedFiberBundle.gain 0 a b i i p * (show ℂ from s p) = 0 at hp
  rw [FixedFiberBundle.gain_self,one_mul] at hp
  exact hp

/-- The first central residual multidegree has no nonzero actual analytic section. -/
theorem residual_one_section_zero
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 (-1) (fun _ => 0)).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 (-1) (fun _ => 0)).TotalSpace)))
    (p : Fiber 0) : s p = 0 :=
  negative_degree_section_zero (-1) (fun _ => 0) (by norm_num [restrictionDegree]) s hs p

/-- The second central residual multidegree has no nonzero actual analytic section. -/
theorem residual_two_section_zero
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 (-1) (fun r => if r = 3 then 1 else 0)).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 (-1) (fun r => if r = 3 then 1 else 0)).TotalSpace)))
    (p : Fiber 0) : s p = 0 :=
  negative_degree_section_zero (-1) (fun r => if r = 3 then 1 else 0)
    (by change (-1 : ℤ) < 0; norm_num) s hs p

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
