import FailureOfSemipositiveMetricExtension.GenericConicDensity

/-! Nearby vanishing for arbitrary actual analytic sections of the ambient
K+mL degree model. The proof uses the constructed conic bundle isomorphism,
projective-line negative-degree vanishing, and a proved dense generic locus. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem negative_degree_section_zero (t : ℂ) (ht : t ≠ 0) (a : ℤ) (b : Fin 4 → ℤ)
    (hdeg : restrictionDegree a b < 0)
    (s : ∀ p : Fiber t, (FixedFiberBundle.core t a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core t a b).TotalSpace)))
    (p : Fiber t) : s p = 0 := by
  have hz : ∀ q ∈ genericLocus t, s q = 0 := by
    intro q hq
    obtain ⟨w,hw,hbase⟩ := hq
    have hv := negative_restriction_section_zero (dataOfVector t ht w hw) a b hdeg s hs
      (Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero t w hw))
    have he := param_dataOfVector t ht q w hw hbase
    change s (param (dataOfVector t ht w hw)
      (Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero t w hw))) = 0 at hv
    rw [he] at hv
    exact hv
  let i := (FixedFiberBundle.core t a b).indexAt p
  let e := (FixedFiberBundle.core t a b).localTriv i
  let f : Fiber t → ℂ := fun q => (e (⟨q,s q⟩ : (FixedFiberBundle.core t a b).TotalSpace)).2
  have hf : ContinuousOn f (FixedFiberBundle.baseSet t i) :=
    continuous_snd.comp_continuousOn (e.continuousOn.comp hs.continuous.continuousOn (fun q hq => hq))
  have hz' : EqOn f (fun _ => 0) (genericLocus t ∩ FixedFiberBundle.baseSet t i) := by
    intro q hq
    change FixedFiberBundle.gain t a b ((FixedFiberBundle.core t a b).indexAt q) i q * (show ℂ from s q) = 0
    rw [hz q hq.1]
    exact mul_zero _
  have hp := hz'.of_subset_closure hf continuousOn_const inter_subset_right
    (by simpa only [inter_comm] using
      (genericLocus_dense t ht).open_subset_closure_inter (FixedFiberBundle.baseSet_isOpen t i))
      ((FixedFiberBundle.core t a b).mem_baseSet_at p)
  change FixedFiberBundle.gain t a b i i p * (show ℂ from s p) = 0 at hp
  rw [FixedFiberBundle.gain_self,one_mul] at hp
  exact hp

/-- Every genuine analytic section of core(1-2m; m-1,m-1,m-1,m-1) is zero
on every nearby fibre, for every integer m. Canonical identification is separately
provided by the already verified Jacobian/top-form modules. -/
theorem nearby_adjoint_section_zero (t : ℂ) (ht : t ≠ 0) (m : ℤ)
    (s : ∀ p : Fiber t, (FixedFiberBundle.core t (1-2*m) (fun _ => m-1)).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core t (1-2*m) (fun _ => m-1)).TotalSpace)))
    (p : Fiber t) : s p = 0 :=
  negative_degree_section_zero t ht (1-2*m) (fun _ => m-1)
    (by rw [adjoint_restrictionDegree]; norm_num) s hs p

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
