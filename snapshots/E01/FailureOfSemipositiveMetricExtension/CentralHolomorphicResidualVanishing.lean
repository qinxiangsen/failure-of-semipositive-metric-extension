import FailureOfSemipositiveMetricExtension.CentralHolomorphicRestrictions

/-! All three residual systems vanish for genuine complex-holomorphic section
maps, at the exact regularity used by the actual structure sheaf. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine.Holomorphic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem negative_degree_section_zero (a : ℤ) (b : Fin 4 → ℤ)
    (hdeg : restrictionDegree a b < 0)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
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
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 (-1) (fun _ => 0)).TotalSpace)))
    (p : Fiber 0) : s p = 0 :=
  negative_degree_section_zero (-1) (fun _ => 0) (by norm_num [restrictionDegree]) s hs p

/-- The second central residual multidegree has no nonzero actual analytic section. -/
theorem residual_two_section_zero
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 (-1) (fun r => if r = 3 then 1 else 0)).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 (-1) (fun r => if r = 3 then 1 else 0)).TotalSpace)))
    (p : Fiber 0) : s p = 0 :=
  negative_degree_section_zero (-1) (fun r => if r = 3 then 1 else 0)
    (by change (-1 : ℤ) < 0; norm_num) s hs p

/-- Zero restricted degree and one actual zero imply zero along the entire line. -/
theorem degree_zero_restriction_section_zero (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (hdeg : restrictionDegree a b = 0)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace)))
    (q : Direction) (hq : s (param c q) = 0) (d : Direction) : s (param c d) = 0 := by
  have hP := projectiveSection_contMDiff c a b s hs
  have hz : projectiveSection c a b s q = 0 := by
    unfold projectiveSection
    rw [hq,map_zero]
  have hall : ∀ d, projectiveSection c a b s d = 0 :=
    ProjectiveLineBundle.holomorphic_section_zero_of_degree_eq_zero
      (restrictionDegree a b) hdeg (projectiveSection c a b s) hP q hz
  apply (restrictionFiberEquiv c a b d).injective
  rw [map_zero]
  exact hall d

/-- Any ambient bundle with degree zero on the transverse lines and negative
degree on ell has no nonzero actual analytic section. -/
theorem zero_line_negative_ell_section_zero (a : ℤ) (b : Fin 4 → ℤ)
    (hline : restrictionDegree a b = 0) (hell : a+b 3 < 0)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace)))
    (p : Fiber 0) : s p = 0 := by
  have he : ∀ d, s (FixedFiberBundle.lineParam d) = 0 :=
    FixedFiberBundle.CurvePullback.Holomorphic.negative_restriction_section_zero a b hell s hs
  have hz : ∀ q ∈ genericLocus, s q = 0 := by
    intro q hq
    obtain ⟨c,d,rfl⟩ := genericLocus_mem_line q hq
    apply degree_zero_restriction_section_zero c a b hline s hs (ProjectiveLine.param 0 0)
    rw [param_intersects_ell]
    exact he _
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
      genericLocus_dense.open_subset_closure_inter (FixedFiberBundle.baseSet_isOpen 0 i))
      ((FixedFiberBundle.core 0 a b).mem_baseSet_at p)
  change FixedFiberBundle.gain 0 a b i i p * (show ℂ from s p) = 0 at hp
  rw [FixedFiberBundle.gain_self,one_mul] at hp
  exact hp

/-- The actual third residual class 2H-E₀-E₁-E₂-2E₃, expressed in the
verified ambient multidegree model, has no nonzero analytic section. -/
theorem residual_three_section_zero
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 (-3) (fun r => if r = 3 then 2 else 1)).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 (-3) (fun r => if r = 3 then 2 else 1)).TotalSpace)))
    (p : Fiber 0) : s p = 0 :=
  zero_line_negative_ell_section_zero (-3) (fun r => if r = 3 then 2 else 1)
    (by rfl) (by change (-1:ℤ) < 0; norm_num) s hs p

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine.Holomorphic
