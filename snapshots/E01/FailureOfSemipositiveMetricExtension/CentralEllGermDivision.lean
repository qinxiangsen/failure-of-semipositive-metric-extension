import FailureOfSemipositiveMetricExtension.GlobalFiberHolomorphicDivision
import FailureOfSemipositiveMetricExtension.GermLocalDivisibility
import FailureOfSemipositiveMetricExtension.CentralDivisorIdeals
import FailureOfSemipositiveMetricExtension.CentralRestrictionWellDefined

/-! Membership in the actual ell divisor stalk ideal produces regular local
complex-holomorphic quotients, and these glue in the actual residual line
bundle. Every quotient and overlap identity is constructed, not assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Manifold Topology TopologicalSpace CategoryTheory Opposite
open scoped Manifold ContDiff

theorem exists_local_ell_quotient {a : ℤ} {b : Fin 4 → ℤ} (N : SectionData 0 a b)
    (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i)
    (hg : sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p) :
    ∃ (V : Opens (Fiber 0)) (f : Fiber 0 → ℂ), p ∈ V ∧ (V : Set (Fiber 0)) ⊆ baseSet 0 i ∧
      ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ f V ∧
      ∀ q ∈ V, f q * ellSection.coefficient i q = N.coefficient i q := by
  classical
  rw [ellPowerStalkIdeal,divisorPowerStalkIdeal_eq_frame ellSection 1 i p hp] at hg
  obtain ⟨V,hpV,j,A,hA⟩ := (FailureOfSemipositiveMetricExtension.Multiplier.germ_mem_power_iff_locally_divisible
    (Fiber 0) (frameOpen 0 i) (coefficientSection ellSection i) (coefficientSection N i) p hp 1).mp hg
  let f : Fiber 0 → ℂ := fun q => if hq : q ∈ V then A ⟨q,hq⟩ else 0
  refine ⟨V,f,hpV,j.le,?_,?_⟩
  · have hres : (fun q : V => f q) = A := by
      funext q
      simp only [f,dif_pos q.2]
    have hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ (fun q : V => f q) := by
      rw [hres]
      exact A.contMDiff
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hs ⟨q,hq⟩)).contMDiffWithinAt
  · intro q hq
    have h := congrArg (fun s : C^∞⟮𝓘(ℂ,FixedFiber.Coord),V;𝓘(ℂ),ℂ⟯ => s ⟨q,hq⟩) hA
    change N.coefficient i q = ellSection.coefficient i q ^ 1 * A ⟨q,hq⟩ at h
    simpa only [f,dif_pos hq,pow_one,mul_comm] using h.symm

structure EllQuotientPatch {a : ℤ} {b : Fin 4 → ℤ} (N : SectionData 0 a b) (p : Fiber 0) where
  frame : Index
  domain : Opens (Fiber 0)
  mem_domain : p ∈ domain
  subset_frame : (domain : Set (Fiber 0)) ⊆ baseSet 0 frame
  coefficient : Fiber 0 → ℂ
  holomorphic : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ∞ coefficient domain
  equation : ∀ q ∈ domain, coefficient q * ellSection.coefficient frame q = N.coefficient frame q

def ellQuotientPatch {a : ℤ} {b : Fin 4 → ℤ} (N : SectionData 0 a b)
    (hN : ∀ i p hp, sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p) (p : Fiber 0) :
    EllQuotientPatch N p := by
  apply Classical.choice
  let i := (core 0 a b).indexAt p
  have hp : p ∈ baseSet 0 i := (core 0 a b).mem_baseSet_at p
  obtain ⟨V,f,hpV,hVi,hf,he⟩ := exists_local_ell_quotient N i p hp (hN i p hp)
  exact ⟨⟨i,V,hpV,hVi,f,hf,he⟩⟩

theorem ell_coefficient_ne_zero_of_value_ne_zero (p : Fiber 0)
    (hp : sectionValue ellSection p ≠ 0) (i : Index) (hi : p ∈ baseSet 0 i) :
    ellSection.coefficient i p ≠ 0 :=
  fun hz => hp ((sectionValue_zero_iff ellSection i p hi).mpr hz)

/-- A genuine holomorphic residual section, with its actual bundle section map. -/
def divideByEll {a : ℤ} {b : Fin 4 → ℤ}
    (N : SectionData 0 (a+(-2)) (fun r => b r+ellDegree r))
    (hN : ∀ i p hp, sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p) :
    Holomorphic.SectionData 0 a b :=
  Holomorphic.divideSections (Holomorphic.ofAnalyticData ellSection) (Holomorphic.ofAnalyticData N)
    {p | sectionValue ellSection p ≠ 0} ell_nonzero_dense ell_coefficient_ne_zero_of_value_ne_zero
    (fun p => (ellQuotientPatch N hN p).domain) (fun p => (ellQuotientPatch N hN p).domain.isOpen)
    (fun p => ⟨p,(ellQuotientPatch N hN p).mem_domain⟩)
    (fun p => (ellQuotientPatch N hN p).frame) (fun p => (ellQuotientPatch N hN p).subset_frame)
    (fun p => (ellQuotientPatch N hN p).coefficient) (fun p => (ellQuotientPatch N hN p).holomorphic)
    (fun p => (ellQuotientPatch N hN p).equation)

theorem divideByEll_coefficient_mul {a : ℤ} {b : Fin 4 → ℤ}
    (N : SectionData 0 (a+(-2)) (fun r => b r+ellDegree r))
    (hN : ∀ i p hp, sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p)
    (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    (divideByEll N hN).coefficient i p * ellSection.coefficient i p = N.coefficient i p :=
  Holomorphic.divideSections_mul_coefficient (Holomorphic.ofAnalyticData ellSection) (Holomorphic.ofAnalyticData N)
    {p | sectionValue ellSection p ≠ 0} ell_nonzero_dense ell_coefficient_ne_zero_of_value_ne_zero
    (fun p => (ellQuotientPatch N hN p).domain) (fun p => (ellQuotientPatch N hN p).domain.isOpen)
    (fun p => ⟨p,(ellQuotientPatch N hN p).mem_domain⟩)
    (fun p => (ellQuotientPatch N hN p).frame) (fun p => (ellQuotientPatch N hN p).subset_frame)
    (fun p => (ellQuotientPatch N hN p).coefficient) (fun p => (ellQuotientPatch N hN p).holomorphic)
    (fun p => (ellQuotientPatch N hN p).equation) i p hp

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
